-- Prove2me | Definitions.Def_GradSuffice_UniformlyBoundedShatteredTrees
-- name    : GradSuffice_UniformlyBoundedShatteredTrees
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:14.674247+00:00
-- url     : https://prove2.me/theorems/4439acc4-a506-44cb-bc0d-9e67d8943146
-- title:
--   Uniformly bounded shattered trees
-- statement:
--   The unit ball $B$ of $X$ has **uniformly bounded shattered trees** if for every margin $\theta>0$ there is a finite bound $d(\theta)$ on the depth of every $B^\star$-valued tree shattered by $B$ at margin $\theta$:
--   $$\forall\theta>0\ \exists d\in\mathbb N:\ \text{every } B^\star\text{-valued tree of depth } m \text{ shattered by } B \text{ at margin } \theta \text{ has } m\le d.$$
--   This is item 2 of Theorem 1.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §3.1, p.7

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_IsShattered

namespace GradSuffice

/-- **Uniformly bounded shattered trees.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §3.1, p.7: "We say that `B` has uniformly
bounded shattered trees if, for every `θ > 0`, there is a finite bound `d(θ)` on the depth of every
`B⋆`-valued tree shattered by `B` at margin `θ`."

**Formalization Note.** `B` is `Metric.closedBall (0 : X) 1`; a tree of depth `m` is a
`NondualOpt.Tree (StrongDual ℝ X) m`. -/
def UniformlyBoundedShatteredTrees (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ θ : ℝ, 0 < θ → ∃ d : ℕ, ∀ (m : ℕ) (ξ : NondualOpt.Tree (StrongDual ℝ X) m),
    IsDualValued ξ → IsShattered (Metric.closedBall (0 : X) 1) θ ξ → m ≤ d

end GradSuffice


