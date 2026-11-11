-- Prove2me | Definitions.Def_SparseLowFactors_BoundedDeg_Sparse
-- name    : SparseLowFactors_BoundedDeg_Sparse
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:22:44.850202+00:00
-- url     : https://prove2.me/theorems/759d04c8-602e-4c22-bfd8-425f140ba8ea
-- title:
--   Sparsity, individual degree, monomial divisors, $g \prec_r h$, truncation, $\mathrm{Esym}_r$
-- statement:
--   Let $F$ be a field and $X=(X_1,\dots,X_n)$. For $f\in F[X]$:
--
--   1. The **sparsity** $\|f\|$ is the number of monomials of $f$ with a non-zero coefficient; $f$ is **$s$-sparse** if $\|f\|\le s$ (p. 25).
--   2. $f$ has **individual degree at most $d$** if $\deg_{X_i} f\le d$ for every $i$ (p. 15).
--   3. $g$ is **not divisible by a monomial** if no non-constant monomial divides $g$, equivalently no variable $X_i$ divides $g$; non-zero constants qualify (Theorem 1.1, Remark 1.4).
--   4. For $f=\sum_{j} c_jX^{\alpha_j}\neq 0$ with $c_j\ne0$, the **maximal monomial divisor** is $\prod_{i=1}^n X_i^{\min_j\alpha_{j,i}}$ (Remark 1.4); the definition records its exponent vector $(\min_j\alpha_{j,1},\dots,\min_j\alpha_{j,n})$.
--   5. **$r$-monomial equivalence** (Definition 2.1): $g\prec_r h$ if $h=gM$ for a monomial $M$ (coefficient $1$) of individual degree at most $r$.
--   6. **Truncation** (Definition 2.7): for $p=\sum_{i\ge0}p_iZ^i$ with coefficients in a ring, $p\ \mathrm{Trunc}\ Z^D=\sum_{0\le i<D}p_iZ^i$.
--   7. $\mathrm{Esym}_r(S)$ is the elementary symmetric polynomial of degree $r$ evaluated at the elements of the finite multiset $S$ (p. 15).
--
--   These are the basic objects in which the main theorem and every milestone are phrased.
--
--   **Formalization Note** Variables are `Fin n` (indices from $0$). The monomial-divisor exponent of the zero polynomial is set to $0$; every statement using it assumes $f\neq0$.
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 15 (§2.1, Definition 2.1), p. 17 (Definition 2.7), p. 25 (§2.7), p. 5 (Remark 1.4)

import Mathlib

set_option autoImplicit false

/-!
# Sparse polynomials, individual degree, monomial divisors, `≺_r`, truncation

Bhattacharjee, Kothary, Rai, Saraf, *Deterministic Algorithms for Low Individual Degree Factors of
Sparse Polynomials*, arXiv:2606.27293 (held version, sha256 9837a932…): §2.1 p. 15 (individual
degree, `Esym`, `Trunc`, Definition 2.1), §2.7 p. 25 (sparsity), Remark 1.4 p. 5 (maximal monomial
divisor), Definition 2.7 p. 17 (truncation).
-/

namespace SparseLowFactors.BoundedDeg

open MvPolynomial

/-- Sparsity `‖f‖` (p. 25): the number of monomials of `f` with a non-zero coefficient. -/
def sparsity {σ F : Type*} [CommSemiring F] (f : MvPolynomial σ F) : ℕ := f.support.card

/-- `f` is `s`-sparse (p. 25): it has at most `s` monomials with non-zero coefficients. -/
def IsSparse {σ F : Type*} [CommSemiring F] (s : ℕ) (f : MvPolynomial σ F) : Prop :=
  sparsity f ≤ s

/-- Individual degree at most `d` (p. 15): the degree of `f` in every variable is at most `d`. -/
def IndDegLE {σ F : Type*} [CommSemiring F] (d : ℕ) (f : MvPolynomial σ F) : Prop :=
  ∀ i : σ, f.degreeOf i ≤ d

/-- `g` is not divisible by a monomial (Theorem 1.1, Remark 1.4): no non-constant monomial divides
`g`, equivalently no variable `X_i` divides `g`. Non-zero constants qualify. -/
def NoMonomialDivisor {σ F : Type*} [CommSemiring F] (g : MvPolynomial σ F) : Prop :=
  ∀ i : σ, ¬ (X i ∣ g)

/-- The exponent vector of the maximal monomial divisor of `f = Σ_j c_j X^{α_j}` (Remark 1.4, p. 5):
`(min_j α_{j,1}, …, min_j α_{j,n})`, the minimum over the monomials in the support of `f`. For
`f = 0` (no maximal monomial divisor exists) the value is `0`; every statement using it assumes
`f ≠ 0`. -/
noncomputable def monDivExp {n : ℕ} {F : Type*} [CommSemiring F] (f : MvPolynomial (Fin n) F) :
    Fin n → ℕ :=
  fun i => if h : f.support.Nonempty then f.support.inf' h (fun m => m i) else 0

/-- `g ≺_r h` (Definition 2.1, p. 15): there is a monomial `M` (coefficient `1`) of individual
degree at most `r` with `h = g M`. -/
def PrecR {σ F : Type*} [CommSemiring F] (r : ℕ) (g h : MvPolynomial σ F) : Prop :=
  ∃ m : σ →₀ ℕ, (∀ i, m i ≤ r) ∧ h = g * monomial m 1

/-- Truncation (Definition 2.7, p. 17, and the notation `P Trunc T^{D+1}` of p. 15) of a
polynomial in one main variable with coefficients in a ring `A`: `p Trunc Z^D = Σ_{0 ≤ i < D} p_i Z^i`,
i.e. all terms of degree at least `D` are discarded. -/
noncomputable def polyTrunc {A : Type*} [Semiring A] (D : ℕ) (p : Polynomial A) : Polynomial A :=
  ∑ i ∈ Finset.range D, Polynomial.monomial i (p.coeff i)

/-- `Esym_r(S)` (p. 15): the elementary symmetric polynomial of degree `r` evaluated at the elements
of the finite multiset `S`. -/
def esym {L : Type*} [CommSemiring L] (r : ℕ) (S : Multiset L) : L := S.esymm r

end SparseLowFactors.BoundedDeg


