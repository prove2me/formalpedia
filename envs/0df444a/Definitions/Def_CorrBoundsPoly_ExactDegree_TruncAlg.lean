-- Prove2me | Definitions.Def_CorrBoundsPoly_ExactDegree_TruncAlg
-- name    : CorrBoundsPoly_ExactDegree_TruncAlg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:57:17.007214+00:00
-- url     : https://prove2.me/theorems/df7c7eea-e36b-47df-b692-a13d183702a2
-- title:
--   Eqs. (3.2), (3.4), (3.6) — the truncated algebra $A_m=\mathbb F_2[x]/(x_i^2)$, $h(F)$ and the rank defect $\nu(F)$
-- statement:
--   For a finite variable set $\iota$ with $|\iota|=m$, the **truncated algebra** is
--   $$A_\iota=\mathbb F_2[x_i:i\in\iota]/(x_i^2:i\in\iota),$$
--   with basis the squarefree monomials $x_S=\prod_{i\in S}x_i$, $S\subseteq\iota$, and dimension $2^m$; $x_Sx_T=x_{S\cup T}$ if $S\cap T=\emptyset$ and $0$ otherwise. It differs from the Boolean function algebra $B=\mathbb F_2[x]/(x_i^2-x_i)$. A polynomial $F$ is **multilinear** when no variable appears with exponent above one; multilinear polynomials are the elements of $A_\iota$ written in the basis $x_S$.
--
--   For a polynomial $F$, let $\mu_F:A_\iota\to A_\iota$, $a\mapsto Fa$, be multiplication by the image of $F$, and put
--   $$h(F)=2^m-2\operatorname{rank}_{A_\iota}\mu_F,\qquad \nu(F)=2^{-m}h(F)=1-2^{1-m}\operatorname{rank}_{A_\iota}\mu_F .$$
--   For $F$ homogeneous of positive degree, $\mu_F^2=0$ and $h(F)=\dim\ker\mu_F-\dim\operatorname{im}\mu_F$; $\nu(F)$ is the **normalized rank defect** of $F$, which the paper shows is the exact degree-$(\deg F-1)$ correlation of its cores.
--
--   **Formalization Note** `TruncAlg ι` is the quotient of `MvPolynomial ι (ZMod 2)` by the ideal spanned by the `X i ^ 2`; `toTrunc` is the quotient map. `mulRank F` is the `ZMod 2`-dimension (`Module.finrank`) of the range of `LinearMap.mulLeft` by `toTrunc F`; `A_ι` is finite-dimensional, so this is its rank. `hA F : ℤ` and `nu F : ℝ` are defined for every `F` (in particular `ν(0)=1`); statements apply them to homogeneous multilinear polynomials, as the paper does.
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), §3.2, pp. 26–27 (PDF 28–29), Eqs. (3.2), (3.3), (3.4), (3.6)

import Mathlib

namespace CorrBoundsPoly.ExactDegree

/-! Xin Li, *More on Correlation Bounds for Polynomials*, STOC 2027 submission (manuscript sha256
aa4ef6f7…), §3.2, pp. 26–27 (PDF 28–29), Eqs. (3.2), (3.4), (3.6).

The truncated algebra `A_ι = F₂[x_i : i ∈ ι]/(x_i²)`, the rank of multiplication by an element,
`h(F) = 2^{|ι|} − 2 rank µ_F` and the normalized rank defect `ν(F) = 2^{−|ι|} h(F)`. -/

/-- A polynomial is multilinear when no variable occurs with exponent above one; multilinear
polynomials are the paper's representation of Boolean polynomials and of elements of `A_ι`
(basis `x_S`, `S ⊆ ι`). -/
def IsMultilinear {ι : Type*} (p : MvPolynomial ι (ZMod 2)) : Prop :=
  ∀ μ ∈ p.support, ∀ i, μ i ≤ 1

/-- **Eq. (3.2).** The truncated algebra `A_ι = F₂[x_i : i ∈ ι]/(x_i² : i ∈ ι)`. It is *not* the
Boolean function algebra `F₂[x]/(x_i² − x_i)` of Eq. (3.3). -/
abbrev TruncAlg (ι : Type*) : Type _ :=
  MvPolynomial ι (ZMod 2) ⧸
    Ideal.span (Set.range fun i : ι => (MvPolynomial.X i : MvPolynomial ι (ZMod 2)) ^ 2)

/-- The image of a polynomial in `A_ι`. -/
noncomputable def toTrunc {ι : Type*} (F : MvPolynomial ι (ZMod 2)) : TruncAlg ι :=
  Ideal.Quotient.mk _ F

/-- `rank_{A_ι} µ_F`: the `F₂`-rank of multiplication `a ↦ F a` on `A_ι`. -/
noncomputable def mulRank {ι : Type*} (F : MvPolynomial ι (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (LinearMap.mulLeft (ZMod 2) (toTrunc F)))

/-- **Eq. (3.4).** `h(F) = 2^{|ι|} − 2 rank µ_F` (rank computed in `A_ι`); for `F` homogeneous of
positive degree this is `dim ker µ_F − dim im µ_F`. -/
noncomputable def hA {ι : Type*} [Fintype ι] (F : MvPolynomial ι (ZMod 2)) : ℤ :=
  2 ^ Fintype.card ι - 2 * (mulRank F : ℤ)

/-- **Eq. (3.6).** `ν(F) = 2^{−m} h(F) = 1 − 2^{1−m} rank_{A_m}(µ_F)` with `m = |ι|`. It is defined
for every `F`; in particular `ν(0) = 1`. -/
noncomputable def nu {ι : Type*} [Fintype ι] (F : MvPolynomial ι (ZMod 2)) : ℝ :=
  1 - 2 * (mulRank F : ℝ) / 2 ^ Fintype.card ι

end CorrBoundsPoly.ExactDegree


