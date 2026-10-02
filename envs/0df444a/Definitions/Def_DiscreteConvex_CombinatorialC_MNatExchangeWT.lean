-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_MNatExchangeWT
-- name    : DiscreteConvex_CombinatorialC_MNatExchangeWT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:42:30.93737+00:00
-- url     : https://prove2.me/theorems/642da8ce-83b5-48bd-85c2-95fe1a650212
-- title:
--   M-natural exchange property, extended-real version
-- statement:
--   As `MNatExchangeR`, restricted to $x,y\in\operatorname{dom}_{\mathbb R}f$ ($f(x)\ne+\infty$).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_CharVec
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.68, axiom (M♮-EXC[R]), extended-real-valued
version for the general (possibly `+∞`) quadratic forms of §2.1.4, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- Axiom **(M-natural-EXC[R])** for a `WithTop ℝ`-valued function `f`, restricted to
`x, y ∈ dom_R f` (`f x ≠ ⊤`, `f y ≠ ⊤`) as the book's own definition requires: for
`i ∈ supp⁺(x-y)`, there exist `j ∈ supp⁻(x-y) ∪ {0}` and `α₀ > 0` such that
`f(x) + f(y) ≥ f(x - α(χ_i-χ_j)) + f(y + α(χ_i-χ_j))` for all `0 ≤ α ≤ α₀`. -/
def MNatExchangeWT {W : Type*} [Fintype W] [DecidableEq W] (f : (W → ℝ) → WithTop ℝ) : Prop :=
  ∀ x y : W → ℝ, f x ≠ ⊤ → f y ≠ ⊤ → ∀ i ∈ SuppPosR (x - y),
    (∃ j ∈ SuppNegR (x - y), ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      f x + f y ≥ f (x - α • (CharVec i - CharVec j)) + f (y + α • (CharVec i - CharVec j))) ∨
    (∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      f x + f y ≥ f (x - α • CharVec i) + f (y + α • CharVec i))

end DiscreteConvex.CombinatorialC


