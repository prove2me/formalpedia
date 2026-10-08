-- Prove2me | Definitions.Def_AMPUniversality_Universal_Poly
-- name    : AMPUniversality_Universal_Poly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:10.868998+00:00
-- url     : https://prove2.me/theorems/20091e0b-4b24-4fc1-8ad2-1378dfb6a336
-- title:
--   (3.1), (4.10), (4.31) — polynomials ℝ^q → ℝ and ℝ^q → ℝ^q of degree ≤ d in coefficient form, monomials x^m, and the Jacobian
-- statement:
--   Fix integers $q \ge 1$ (the dimension of each coordinate) and $d \ge 0$ (a degree bound). An **exponent vector** is $m = (m(1), \dots, m(q))$ with nonnegative integer entries, and the **monomial** of $x = (x(1), \dots, x(q)) \in \mathbb R^q$ with exponent $m$ is
--
--   $$
--   x^m \;=\; \prod_{r=1}^q x(r)^{m(r)} .
--   $$
--
--   A real polynomial $p : \mathbb R^q \to \mathbb R$ of degree at most $d$ is given by its coefficients $p_m$, indexed by the exponent vectors with $m(1) + \dots + m(q) \le d$:
--
--   $$
--   p(x) \;=\; \sum_{m(1)+\cdots+m(q) \le d} p_m \, \prod_{s=1}^q x(s)^{m(s)} .
--   $$
--
--   A polynomial map $f : \mathbb R^q \to \mathbb R^q$ of degree at most $d$ is given by coefficients $c(r, m)$, one polynomial per output coordinate $r \in [q]$, exactly as in display (4.10) of the paper: $f_r(x) = \sum_{m} c(r,m) \prod_s x(s)^{m(s)}$. Its **Jacobian** at $x$ is the $q \times q$ matrix with entries
--
--   $$
--   \frac{\partial f_r}{\partial x(s)}(x) \;=\; \sum_{m} c(r,m)\, m(s)\, x(s)^{m(s)-1} \prod_{s' \ne s} x(s')^{m(s')} .
--   $$
--
--   These are the polynomial nonlinearities of a $(C,d)$-regular polynomial sequence of AMP instances, the test polynomials $p_{N,i}$ of Theorem 3, and the moments $\mathbb E[(z^t_i)^m]$ of Propositions 1 and 3.
--
--   **Formalization Note** Coordinates are indexed by `Fin q` (0-based). An exponent vector has entries in `Fin (d+1)` and only those with total degree at most $d$ are summed (`degLe d q`); the monomial `monomial x m` takes an arbitrary $m \in \mathbb N^q$. In the Jacobian the term with $m(s) = 0$ carries the factor $m(s) = 0$, so the truncated natural-number exponent $m(s) - 1$ never matters. Coefficient vectors rather than `MvPolynomial` are used so that random polynomials (Definition 4(2)) live in a measurable space.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 13, (3.1); p. 17, (4.10); p. 29, (4.31); p. 7, (1.5)

import Mathlib

namespace AMPUniversality.Universal

open Finset

/-- The exponent vectors `m = (m(1), …, m(q))`, each `m(s) ≤ d`, of total degree
`m(1) + ⋯ + m(q) ≤ d`: the index set of the coefficient form (4.10). -/
def degLe (d q : ℕ) : Finset (Fin q → Fin (d + 1)) :=
  univ.filter (fun m => ∑ s, (m s : ℕ) ≤ d)

/-- The monomial `x^m = ∏_{r=1}^q x(r)^{m(r)}` of (3.1), for `x ∈ ℝ^q` and `m ∈ ℕ^q`. -/
def monomial {q : ℕ} (x : Fin q → ℝ) (m : Fin q → ℕ) : ℝ :=
  ∏ r, x r ^ m r

/-- A real polynomial `p : ℝ^q → ℝ` of degree at most `d` in coefficient form:
`p(x) = ∑_{m(1)+⋯+m(q) ≤ d} p_m ∏_s x(s)^{m(s)}` (cf. (4.10), (4.31)). -/
def polyEval1 {d q : ℕ} (p : (Fin q → Fin (d + 1)) → ℝ) (x : Fin q → ℝ) : ℝ :=
  ∑ m ∈ degLe d q, p m * ∏ s, x s ^ (m s : ℕ)

/-- A polynomial map `f : ℝ^q → ℝ^q` of degree at most `d` in coefficient form (4.10):
its `r`-th coordinate is `f_r(x) = ∑_{m(1)+⋯+m(q) ≤ d} c(r, m) ∏_s x(s)^{m(s)}`. -/
def polyEval {d q : ℕ} (c : Fin q → (Fin q → Fin (d + 1)) → ℝ) (x : Fin q → ℝ) (r : Fin q) : ℝ :=
  polyEval1 (c r) x

/-- The Jacobian of the polynomial map `polyEval c` at `x`: entry `(r, s)` is
`∂f_r/∂x(s)(x) = ∑_m c(r, m) · m(s) · x(s)^{m(s)-1} · ∏_{s' ≠ s} x(s')^{m(s')}`.
(When `m(s) = 0` the factor `m(s)` vanishes, so the truncated exponent `m(s) - 1` is harmless.) -/
def polyJac {d q : ℕ} (c : Fin q → (Fin q → Fin (d + 1)) → ℝ) (x : Fin q → ℝ)
    (r s : Fin q) : ℝ :=
  ∑ m ∈ degLe d q, c r m * ((m s : ℕ) : ℝ) * x s ^ ((m s : ℕ) - 1) *
    ∏ s' ∈ univ.erase s, x s' ^ (m s' : ℕ)

end AMPUniversality.Universal


