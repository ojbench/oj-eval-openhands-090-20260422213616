#ifndef SRC_HPP
#define SRC_HPP

#include <bits/stdc++.h>
#include "fraction.hpp"

class matrix {
private:
    int m, n;
    fraction **data;

    void allocate(int m_, int n_) {
        m = m_; n = n_;
        if (m == 0 || n == 0) {
            data = nullptr;
            return;
        }
        data = new fraction*[m];
        for (int i = 0; i < m; ++i) {
            data[i] = new fraction[n];
        }
    }

    void deallocate() {
        if (!data) return;
        for (int i = 0; i < m; ++i) delete [] data[i];
        delete [] data;
        data = nullptr; m = n = 0;
    }

public:
    matrix() { m = n = 0; data = nullptr; }

    matrix(int m_, int n_) { data = nullptr; allocate(m_, n_); }

    matrix(const matrix &obj) {
        data = nullptr;
        allocate(obj.m, obj.n);
        for (int i = 0; i < m; ++i)
            for (int j = 0; j < n; ++j)
                data[i][j] = obj.data[i][j];
    }

    matrix(matrix &&obj) noexcept {
        m = obj.m; n = obj.n; data = obj.data;
        obj.m = obj.n = 0; obj.data = nullptr;
    }

    ~matrix() { deallocate(); }

    matrix &operator=(const matrix &obj) {
        if (this == &obj) return *this;
        deallocate();
        allocate(obj.m, obj.n);
        for (int i = 0; i < m; ++i)
            for (int j = 0; j < n; ++j)
                data[i][j] = obj.data[i][j];
        return *this;
    }

    fraction &operator()(int i, int j) {
        // i is 1-based row index, j is 0-based column index
        if (i < 1 || i > m || j < 0 || j >= n) throw matrix_error();
        return data[i - 1][j];
    }

    friend matrix operator*(const matrix &lhs, const matrix &rhs) {
        if (lhs.n == 0 || rhs.m == 0) throw matrix_error();
        if (lhs.n != rhs.m) throw matrix_error();
        matrix res(lhs.m, rhs.n);
        for (int i = 0; i < lhs.m; ++i) {
            for (int k = 0; k < lhs.n; ++k) {
                const fraction &lik = lhs.data[i][k];
                if (lik == fraction(0)) continue;
                for (int j = 0; j < rhs.n; ++j) {
                    res.data[i][j] = res.data[i][j] + lik * rhs.data[k][j];
                }
            }
        }
        return res;
    }

    matrix transposition() {
        if (m == 0 || n == 0) throw matrix_error();
        matrix res(n, m);
        for (int i = 0; i < m; ++i)
            for (int j = 0; j < n; ++j)
                res.data[j][i] = data[i][j];
        return res;
    }

    fraction determination() {
        if (m == 0 || n == 0) throw matrix_error();
        if (m != n) throw matrix_error();
        int sz = n;
        std::vector<std::vector<fraction>> a(sz, std::vector<fraction>(sz));
        for (int i = 0; i < sz; ++i)
            for (int j = 0; j < sz; ++j)
                a[i][j] = data[i][j];
        fraction det(1);
        bool sign_pos = true;
        for (int col = 0, row = 0; col < sz && row < sz; ++col, ++row) {
            int pivot = -1;
            for (int i = row; i < sz; ++i) {
                if (!(a[i][col] == fraction(0))) { pivot = i; break; }
            }
            if (pivot == -1) {
                return fraction(0);
            }
            if (pivot != row) {
                std::swap(a[pivot], a[row]);
                sign_pos = !sign_pos;
            }
            fraction piv = a[row][col];
            det = det * piv;
            for (int i = row + 1; i < sz; ++i) {
                if (a[i][col] == fraction(0)) continue;
                fraction factor = a[i][col] / piv;
                for (int j = col; j < sz; ++j) {
                    a[i][j] = a[i][j] - factor * a[row][j];
                }
            }
        }
        if (!sign_pos) det = fraction(0) - det; // negate
        return det;
    }

    // helpers
    int rows() const { return m; }
    int cols() const { return n; }
    const fraction &at0(int i, int j) const { return data[i][j]; }
};

class resistive_network {
private:
    int interface_size, connection_size;
    matrix adjacency, conduction;
    std::vector<int> from_idx, to_idx;
    std::vector<fraction> resistance, conductance;
    matrix laplacian; // A^T C A
    matrix reduced_K; // remove last row and column

    void build_laplacian() {
        matrix AT = adjacency.transposition();
        matrix AC = conduction * adjacency;
        laplacian = AT * AC;
        // build reduced_K by removing last row and column
        int n = interface_size;
        reduced_K = matrix(n - 1, n - 1);
        for (int i = 0; i < n - 1; ++i)
            for (int j = 0; j < n - 1; ++j)
                reduced_K(i + 1, j) = laplacian.at0(i, j);
    }

    std::vector<fraction> solve_reduced(const std::vector<fraction> &b) const {
        int n = interface_size - 1;
        std::vector<std::vector<fraction>> a(n, std::vector<fraction>(n + 1));
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) a[i][j] = reduced_K.at0(i, j);
            a[i][n] = b[i];
        }
        // Gaussian elimination
        for (int col = 0, row = 0; col < n && row < n; ++col, ++row) {
            int pivot = -1;
            for (int i = row; i < n; ++i) if (!(a[i][col] == fraction(0))) { pivot = i; break; }
            if (pivot == -1) {
                // singular, but per problem, guaranteed solvable
                continue;
            }
            if (pivot != row) std::swap(a[pivot], a[row]);
            fraction piv = a[row][col];
            for (int j = col; j <= n; ++j) a[row][j] = a[row][j] / piv;
            for (int i = 0; i < n; ++i) if (i != row) {
                if (a[i][col] == fraction(0)) continue;
                fraction factor = a[i][col];
                for (int j = col; j <= n; ++j) a[i][j] = a[i][j] - factor * a[row][j];
            }
        }
        std::vector<fraction> x(n);
        for (int i = 0; i < n; ++i) x[i] = a[i][n];
        return x;
    }

public:
    resistive_network(int interface_size_, int connection_size_, int from[], int to[], fraction resistance_[]) :
        interface_size(interface_size_), connection_size(connection_size_), adjacency(connection_size_, interface_size_), conduction(connection_size_, connection_size_), laplacian(), reduced_K() {
        from_idx.resize(connection_size);
        to_idx.resize(connection_size);
        resistance.resize(connection_size);
        conductance.resize(connection_size);
        for (int k = 0; k < connection_size; ++k) {
            from_idx[k] = from[k] - 1;
            to_idx[k] = to[k] - 1;
            resistance[k] = resistance_[k];
            conductance[k] = fraction(1) / resistance_[k];
            // adjacency row k
            adjacency(k + 1, from_idx[k]) = adjacency(k + 1, from_idx[k]) + fraction(1);
            adjacency(k + 1, to_idx[k]) = adjacency(k + 1, to_idx[k]) - fraction(1);
            // conduction diag
            conduction(k + 1, k) = conductance[k];
        }
        build_laplacian();
    }

    ~resistive_network() = default;

    fraction get_equivalent_resistance(int interface_id1, int interface_id2) {
        int a = interface_id1 - 1;
        int b = interface_id2 - 1;
        std::vector<fraction> I(interface_size, fraction(0));
        I[a] = I[a] + fraction(1);
        I[b] = I[b] - fraction(1);
        // build reduced rhs excluding last node
        std::vector<fraction> bvec(interface_size - 1);
        for (int i = 0; i < interface_size - 1; ++i) bvec[i] = I[i];
        std::vector<fraction> U = solve_reduced(bvec);
        fraction ua = (a == interface_size - 1) ? fraction(0) : U[a];
        fraction ub = (b == interface_size - 1) ? fraction(0) : U[b];
        return ua - ub;
    }

    fraction get_voltage(int id, fraction current[]) {
        // id < interface_size, and u_n = 0
        std::vector<fraction> bvec(interface_size - 1);
        for (int i = 0; i < interface_size - 1; ++i) bvec[i] = current[i];
        std::vector<fraction> U = solve_reduced(bvec);
        return U[id - 1];
    }

    fraction get_power(fraction voltage[]) {
        fraction total(0);
        for (int k = 0; k < connection_size; ++k) {
            fraction dv = voltage[from_idx[k]] - voltage[to_idx[k]];
            total = total + conductance[k] * dv * dv;
        }
        return total;
    }
};


#endif // SRC_HPP
