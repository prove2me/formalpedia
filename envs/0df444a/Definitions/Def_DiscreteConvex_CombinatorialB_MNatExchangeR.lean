-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_MNatExchangeR
-- name    : DiscreteConvex_CombinatorialB_MNatExchangeR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:32:35.694557+00:00
-- url     : https://prove2.me/theorems/855cdb07-7709-4742-a46f-2e7557de8c10
-- title:
--   Real M-natural exchange property (M♮-EXC[R])
-- statement:
--   Axiom $(\mathrm{M}^\natural\text{-EXC}[\mathbb R])$: for $x,y\in\mathbb R^V$ and $i\in\operatorname{supp}^+(x-y)$, there exist $j\in\operatorname{supp}^-(x-y)\cup\{0\}$ and $\alpha_0>0$ such that $f(x)+f(y)\ge f(x-\alpha(\chi_i-\chi_j))+f(y+\alpha(\chi_i-\chi_j))$ for all $0\le\alpha\le\alpha_0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.68

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_CharVec
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.68: the real M-natural exchange property
(the book's `(M♮-EXC[R])`), in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- Axiom **(M-natural-EXC[R])**: for `x, y : Rⱽ` and `i ∈ supp⁺(x-y)`, there exist
`j ∈ supp⁻(x-y) ∪ {0}` (the two disjuncts below) and `α₀ > 0` such that
`f(x) + f(y) ≥ f(x - α(χ_i - χ_j)) + f(y + α(χ_i - χ_j))` for all `0 ≤ α ≤ α₀`; the case
`j = 0` (so `χ_j = 0`) is the second disjunct. -/
def MNatExchangeR {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℝ) → ℝ) : Prop :=
  ∀ x y : V → ℝ, ∀ i ∈ SuppPosR (x - y),
    (∃ j ∈ SuppNegR (x - y), ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      f x + f y ≥ f (x - α • (CharVec i - CharVec j)) + f (y + α • (CharVec i - CharVec j))) ∨
    (∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      f x + f y ≥ f (x - α • CharVec i) + f (y + α • CharVec i))

end DiscreteConvex.CombinatorialB


