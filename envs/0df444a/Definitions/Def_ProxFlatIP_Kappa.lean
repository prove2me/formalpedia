-- Prove2me | Definitions.Def_ProxFlatIP_Kappa
-- name    : ProxFlatIP_Kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:14:25.341004+00:00
-- url     : https://prove2.me/theorems/07f98d94-250a-433d-b5c6-848c8f3030a4
-- title:
--   The parameters $\kappa_I$, $\kappa_d$, the polytope $P_\alpha$ and $\mathrm{vol}_{n-1}$
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $\alpha\in\mathbb Z^n$.
--
--   1. $\kappa_I(A,b,\alpha)$ is the number satisfying
--   $$\max_{x\in P_I(A,b)}\alpha^\top x=\kappa_I(A,b,\alpha)\,\Delta^\alpha_I(A).$$
--   2. For a dimension $d$,
--   $$\kappa_d(A,b,\alpha):=\max_{I:\ \dim P_I(A,b)=d}\kappa_I(A,b,\alpha),$$
--   over the admissible index sets $I$.
--   3. $P_\alpha:=\{x\in\mathbb R^n: |Ax|\le\mathbf 1,\ \alpha^\top x=0\}$, with $|Ax|\le\mathbf 1$ componentwise.
--   4. $\mathrm{vol}_{n-1}$ is the $(n-1)$-dimensional Lebesgue measure on the hyperplane $\alpha^\top x=0$, and $\|\alpha\|_2$ is the Euclidean norm.
--
--   The parameters $\kappa$ measure how far a linear form can reach over a slice, in units of $\Delta^\alpha_I$. The paper bounds them in dimensions $1,2,3$ and adds those bounds up along a path to bound them in every dimension.
--
--   **Formalization Note** The maximum is `sSup` in `ℝ`, and $\kappa_I$ is the quotient, with `x / 0 = 0`. When $\Delta^\alpha_I=0$, $\alpha$ lies in the row space of $A_I$ and $\alpha^\top x=0$ on $P_I$, so equation (2) leaves $\kappa_I$ free and it is taken to be $0$. An empty family gives $\kappa_d=0$. The hyperplane is an inner-product subspace of `EuclideanSpace ℝ (Fin n)` carrying its canonical `volume`, under which a unit cube of an orthonormal basis has measure $1$. It is requested by name, `measureSpaceOfInnerProductSpace`, because the subtype instance would give $0$ on a hyperplane.
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, eq. (2) and the definition of κ_d, p.5; P_α and vol_i, p.6

import Mathlib
import Definitions.Def_ProxFlatIP_Minors

open Matrix
open scoped ENNReal

namespace ProxFlatIP

/-! # The parameters `κ_I`, `κ_d`, and the polytope `P_α` with its `(n−1)`-volume

Celaya–Kuhlmann–Paat–Weismantel, arXiv:2211.14941v1 (preprint): eq. (2), p.5, and p.6.

**Formalization Note.** The paper's `max` is `sSup` in `ℝ`. Under the hypotheses of the lemmas of
this mission the maximum is attained. Two default values are relevant:

* `κ_I` is a quotient, with Lean's `x / 0 = 0`. `Δ^α_I = 0` happens only when `α` lies in the row
  space of `A_I`, and then `α⊤x = 0` on `P_I`, so `(2)` holds and leaves `κ_I` free; `0` is the choice.
* `κ_d` may range over no index set; `sSup ∅ = 0` is then its value. -/

variable {m n : ℕ}

/-- `κ_I(A,b,α)`, the number satisfying `max_{x ∈ P_I(A,b)} α⊤x = κ_I(A,b,α) Δ^α_I(A)`
(eq. (2), p.5). -/
noncomputable def kappaI (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (α : Fin n → ℤ)
    (I : Finset (Fin m)) : ℝ :=
  sSup ((fun x => castVec α ⬝ᵥ x) '' PI A b I) / deltaAlphaI A α I

/-- `κ_d(A,b,α) := max_{I : dim P_I(A,b) = d} κ_I(A,b,α)` (p.5), over the index sets `I` for which
`P_I` is defined (`Admissible`). There are finitely many of them. -/
noncomputable def kappaD (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (α : Fin n → ℤ)
    (d : ℕ) : ℝ :=
  sSup (kappaI A b α '' {I | Admissible A I ∧ dimLin (PI A b I) = d})

/-- `P_α := {x ∈ ℝⁿ : |Ax| ≤ 1, α⊤x = 0}` (p.6), with `|Ax| ≤ 1` componentwise. -/
def Palpha (A : Matrix (Fin m) (Fin n) ℤ) (α : Fin n → ℤ) : Set (Fin n → ℝ) :=
  {x | (∀ i, |(realMat A *ᵥ x) i| ≤ 1) ∧ castVec α ⬝ᵥ x = 0}

/-- `α` as a vector of the Euclidean space `ℝⁿ`. -/
noncomputable def euclidVec (α : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (castVec α)

/-- The hyperplane `α⊤x = 0`, as an inner-product subspace of Euclidean `ℝⁿ`. -/
noncomputable def hyperplane (α : Fin n → ℤ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  (Submodule.span ℝ {euclidVec α})ᗮ

/-- `vol_{n−1}(S)` for `S` in the hyperplane `α⊤x = 0`: the `(n−1)`-dimensional Lebesgue measure of
that hyperplane (p.6).

**Formalization Note.** The measure is the canonical `volume` of the finite-dimensional inner-product
space `hyperplane α` (a unit cube of an orthonormal basis has measure `1`). It is requested through
`measureSpaceOfInnerProductSpace` by name: the subtype instance would give the restriction of
`n`-dimensional Lebesgue measure, which vanishes on a hyperplane. It is not `μH[n−1]`, which differs
from Lebesgue measure by a constant. -/
noncomputable def volHyper (α : Fin n → ℤ) (S : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  (measureSpaceOfInnerProductSpace (E := hyperplane α)).volume
    {w | (w : EuclideanSpace ℝ (Fin n)).ofLp ∈ S}

end ProxFlatIP


