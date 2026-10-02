-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_MNatExchangePlusR
-- name    : DiscreteConvex_CombinatorialB_MNatExchangePlusR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:32:51.19992+00:00
-- url     : https://prove2.me/theorems/3b17e010-cbe2-47f1-8e08-d7ce9e07c6fe
-- title:
--   Strict real M-natural exchange property (M♮-EXC+[R])
-- statement:
--   Axiom $(\mathrm{M}^\natural\text{-EXC}^+[\mathbb R])$: as $(\mathrm{M}^\natural\text{-EXC}[\mathbb R])$, with the inequality strict and $0<\alpha<\alpha_0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_CharVec
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.69: the strict real M-natural exchange
property (the book's `(M♮-EXC+[R])`), in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- Axiom **(M-natural-EXC+[R])**: as `MNatExchangeR`, but with strict inequality
`f(x) + f(y) > f(x - α(χ_i-χ_j)) + f(y + α(χ_i-χ_j))` for all `0 < α < α₀`. -/
def MNatExchangePlusR {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℝ) → ℝ) : Prop :=
  ∀ x y : V → ℝ, ∀ i ∈ SuppPosR (x - y),
    (∃ j ∈ SuppNegR (x - y), ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 < α → α < α0 →
      f x + f y > f (x - α • (CharVec i - CharVec j)) + f (y + α • (CharVec i - CharVec j))) ∨
    (∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 < α → α < α0 →
      f x + f y > f (x - α • CharVec i) + f (y + α • CharVec i))

end DiscreteConvex.CombinatorialB


