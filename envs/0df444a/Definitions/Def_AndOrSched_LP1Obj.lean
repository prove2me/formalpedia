-- Prove2me | Definitions.Def_AndOrSched_LP1Obj
-- name    : AndOrSched_LP1Obj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:55.099588+00:00
-- url     : https://prove2.me/theorems/2e0436a4-ad73-42f3-887c-37b3125d2fc9
-- title:
--   Objective (1a) of LP (1)
-- statement:
--   $$\sum_{b\in B}\sum_{t=1}^{T}w_b\cdot t\cdot x_{bt}.$$
--   Only $B$-jobs appear, because a normalized instance has $w_a=0$ on $A$.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.7, (1a)

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_horizon
open scoped Classical NNReal

namespace AndOrSched

/-- The objective (1a) of LP (1), `Σ_{b∈B} Σ_{t=1}^{T} w_b · t · x_{bt}` (Happach, Schulz, arXiv:2001.07011v1, §2, p.7). It sums
over `B` only, because a normalized instance has `w_a = 0` for `a ∈ A`. -/
def LP1Obj (I : Instance) (x : I.N → ℕ → ℝ) : ℝ :=
  ∑ b, (I.w (Sum.inr b) : ℝ) * ∑ t ∈ Finset.Icc 1 (horizon I), (t : ℝ) * x (Sum.inr b) t

end AndOrSched


