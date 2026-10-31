-- Prove2me | Definitions.Def_PCLAssort_EpsConvex
-- name    : PCLAssort_EpsConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:16.730036+00:00
-- url     : https://prove2.me/theorems/2ac7a5dc-c16f-4959-afce-c15f09950d16
-- title:
--   $\epsilon$-convexity (Definition 3)
-- statement:
--   A function $F:[0,1]^n\to\mathbb R$ has the $\epsilon$-convexity property for sizes $s$ if for each $i,j$ and every $x\in[0,1]^n$ the function
--
--   $$
--   \phi(x,i,j,\epsilon)=F\Big(x_1,\dots,x_i+\epsilon,\dots,x_j-\tfrac{s_i}{s_j}\epsilon,\dots,x_n\Big)
--   $$
--
--   is convex in $\epsilon$ on $\big[-\min\{x_i,\tfrac{s_j}{s_i}(1-x_j)\},\ \min\{1-x_i,\tfrac{s_j}{s_i}x_j\}\big]$.
--
--   This is what makes pipage rounding work: a convex function on an interval containing $0$ is maximized at an endpoint, so one of the two extreme moves does not decrease $F$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Definition 3, p.794 (PDF p.10)

import Mathlib
import Definitions.Def_PCLAssort_pipageMove
import Definitions.Def_PCLAssort_pipageEpsLo
import Definitions.Def_PCLAssort_pipageEpsHi

namespace PCLAssort

/-- Definition 3 (ε-convexity) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.794): for each `i, j` and `x ∈ [0,1]^n`, the function
`φ(x, i, j, ε) = F(x_1, …, x_i + ε, …, x_j − (s_i/s_j) ε, …, x_n)` is convex in `ε` for
`ε ∈ [−min{x_i, (s_j/s_i)(1 − x_j)}, min{(1 − x_i), (s_j/s_i) x_j}]`.

**Formalization Note.** `[0,1]^n` is `Set.Icc 0 1` in the pointwise order of `V → ℝ`. As printed,
the pair `i = j` is not excluded; with `s_i ≠ 0` the move is then constant in `ε`. -/
def EpsConvex {V : Type} [DecidableEq V] (s : V → ℝ) (F : (V → ℝ) → ℝ) : Prop :=
  ∀ i j : V, ∀ x : V → ℝ, x ∈ Set.Icc (0 : V → ℝ) 1 →
    ConvexOn ℝ (Set.Icc (pipageEpsLo s x i j) (pipageEpsHi s x i j))
      (fun ε => F (pipageMove s x i j ε))

end PCLAssort


