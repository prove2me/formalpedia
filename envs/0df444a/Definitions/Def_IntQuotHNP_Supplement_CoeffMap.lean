-- Prove2me | Definitions.Def_IntQuotHNP_Supplement_CoeffMap
-- name    : IntQuotHNP_Supplement_CoeffMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:02:55.462924+00:00
-- url     : https://prove2.me/theorems/d839c3fe-f7dd-4cc7-bee9-62c7b2f06f05
-- title:
--   Definition 2.3 — the scaled nonconstant coefficient map $\Phi$ of a polynomial family
-- statement:
--   Fix an integer $X\ge1$ and integer polynomials $P_1,\dots,P_m\in\mathbb Z[x_1,\dots,x_k]$. Let $M_1,\dots,M_d$ be the distinct **nonconstant monomials** that occur in these polynomials. For an integer polynomial $f=c_0+\sum_{a=1}^d c_aM_a+\cdots$ put
--   $$
--   \Phi(f)=\bigl(c_1X^{\deg M_1},\dots,c_dX^{\deg M_d}\bigr)\in\mathbb Z^d\subseteq\mathbb R^d ,
--   $$
--   where $\deg$ is the total degree. The vectors $\Phi(P_1),\dots,\Phi(P_m)$ generate the lattice of the recovery algorithm, and $v_{\mathrm{tar}}=\Phi(px_1)$ is its target vector.
--
--   **Formalization Note** A monomial is its exponent vector; the coordinates of $\Phi(f)$ are indexed by the finite set of nonzero exponent vectors occurring in some $P_i$, so $d$ is its cardinality. The vector lives in Euclidean space, so norms and inner products are the paper's. Coefficients of $f$ at monomials outside this set are not recorded, as in the paper, where $\Phi$ is applied to integer combinations of the $P_i$.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 2.3, p.14 (PDF p.15)

import Mathlib

namespace IntQuotHNP

namespace Supplement

open Classical in
/-- **The distinct nonconstant monomials of a polynomial family** (Definition 2.3).
Kang, Lee, *Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number
Problems*, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 2.3, p.14 (PDF p.15):
"Fix an integer X ≥ 1 and integer polynomials P₁, . . . , P_m ∈ ℤ[x₁, . . . , x_k]. Let
M₁, . . . , M_d be the distinct nonconstant monomials appearing in these polynomials, in a fixed
order."

`mons P` is the finite set of exponent vectors `s ≠ 0` that occur with nonzero coefficient in some
`P i`; its cardinality is the paper's `d`.

**Formalization Note.** A monomial is its exponent vector `s : σ →₀ ℕ`; "nonconstant" is `s ≠ 0`.
The fixed order of the paper is irrelevant to every statement (norms, inner products and linear
independence do not depend on it), so the coordinates are indexed by the set itself. -/
noncomputable def mons {ι σ : Type*} [Fintype ι] (P : ι → MvPolynomial σ ℤ) :
    Finset (σ →₀ ℕ) :=
  (Finset.univ.biUnion fun i => (P i).support).filter fun s => s ≠ 0

/-- **The scaled nonconstant coefficient map `Φ`** (Definition 2.3).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 2.3, p.14 (PDF p.15):
"For any polynomial of the form f(x) = c₀ + ∑_{a=1}^d c_a M_a(x), c₀, . . . , c_d ∈ ℤ, define
Φ(f) = (c₁X^{deg M₁}, . . . , c_d X^{deg M_d}) ∈ ℤ^d, where deg denotes total degree."

`Phi X P f` is the vector in `ℝ^d` (coordinates indexed by `mons P`) whose entry at the monomial
`s` is `coeff_s(f) · X^{deg s}`.

**Formalization Note.** The vector lives in `EuclideanSpace ℝ (mons P)`, the paper's `ℤ^d ⊆ ℝ^d`
with its Euclidean norm. `f` may be any integer polynomial; coefficients of monomials outside
`mons P` are not recorded, as in the paper, where `Φ` is applied only to integer combinations of the
`P i`. `deg s = ∑ᵢ sᵢ` is the total degree. -/
noncomputable def Phi {ι σ : Type*} [Fintype ι] (X : ℕ) (P : ι → MvPolynomial σ ℤ)
    (f : MvPolynomial σ ℤ) : EuclideanSpace ℝ (mons P) :=
  WithLp.toLp 2 fun s => ((MvPolynomial.coeff s.1 f : ℤ) : ℝ) * (X : ℝ) ^ (s.1.degree)

end Supplement

end IntQuotHNP


