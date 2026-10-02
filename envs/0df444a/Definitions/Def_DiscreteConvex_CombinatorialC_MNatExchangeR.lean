-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_MNatExchangeR
-- name    : DiscreteConvex_CombinatorialC_MNatExchangeR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:41:27.164484+00:00
-- url     : https://prove2.me/theorems/5eea80f0-ea3b-484e-bc2b-cedd1152b263
-- title:
--   Real M-natural exchange property (M♮-EXC[R])
-- statement:
--   $(\mathrm{M}^\natural\text{-EXC}[\mathbb R])$: for $i\in\operatorname{supp}^+(x-y)$, $\exists j\in\operatorname{supp}^-(x-y)\cup\{0\},\ \alpha_0>0$ with $f(x)+f(y)\ge f(x-\alpha(\chi_i-\chi_j))+f(y+\alpha(\chi_i-\chi_j))$, $0\le\alpha\le\alpha_0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_CharVec
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.68: the real M-natural exchange property
(`(M♮-EXC[R])`), in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- Axiom **(M-natural-EXC[R])**: for `x, y : Rᵂ` and `i ∈ supp⁺(x-y)`, there exist
`j ∈ supp⁻(x-y) ∪ {0}` and `α₀ > 0` such that
`f(x) + f(y) ≥ f(x - α(χ_i - χ_j)) + f(y + α(χ_i - χ_j))` for all `0 ≤ α ≤ α₀`. -/
def MNatExchangeR {W : Type*} [Fintype W] [DecidableEq W] (f : (W → ℝ) → ℝ) : Prop :=
  ∀ x y : W → ℝ, ∀ i ∈ SuppPosR (x - y),
    (∃ j ∈ SuppNegR (x - y), ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      f x + f y ≥ f (x - α • (CharVec i - CharVec j)) + f (y + α • (CharVec i - CharVec j))) ∨
    (∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      f x + f y ≥ f (x - α • CharVec i) + f (y + α • CharVec i))

end DiscreteConvex.CombinatorialC


