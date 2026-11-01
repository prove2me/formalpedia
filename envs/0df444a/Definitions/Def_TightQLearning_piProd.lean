-- Prove2me | Definitions.Def_TightQLearning_piProd
-- name    : TightQLearning_piProd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:48.410313+00:00
-- url     : https://prove2.me/theorems/803ea90f-a35e-4ee5-a13d-7e218b45bb20
-- title:
--   (85) — ordered products of $P^{\pi}$
-- statement:
--   For a list of deterministic policies $[\pi_1,\dots,\pi_h]$ and a function $f$, this is the ordered product
--   $$\Big(\prod_{k=1}^hP^{\pi_k}\Big)f=P^{\pi_1}\big(P^{\pi_2}(\cdots P^{\pi_h}f)\big),$$
--   with the rightmost factor acting first and the empty product equal to the identity. It is the product appearing in the total-variance bound of Lemma 5.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), (85), p.25

import Mathlib
import Definitions.Def_TightQLearning_PiOp

namespace TightQLearning

/-- The ordered product `∏_{k=1}^h P^{π_k}` of (85) (arXiv:2102.06548v4, Lemma 5, p.25) applied to
`f`: for the list `[π₁, …, π_h]` this is `P^{π₁}(P^{π₂}(⋯ P^{π_h} f))`, the rightmost factor acting
first. The empty product is the identity. -/
noncomputable def piProd {X A : Type} [Fintype X] (M : QLearning.Convergence.FiniteMDP X A) :
    List (X → A) → (X → A → ℝ) → X → A → ℝ
  | [], f => f
  | π :: l, f => PiOp M π (piProd M l f)

end TightQLearning


