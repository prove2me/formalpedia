-- Prove2me | Definitions.Def_AndOrSched_LP5Obj
-- name    : AndOrSched_LP5Obj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:12.201622+00:00
-- url     : https://prove2.me/theorems/ec2911e3-6c73-4359-9344-5cda7faefb7e
-- title:
--   Objective (5a) of LP (5)
-- statement:
--   $$\sum_{b\in B}\sum_{l=1}^{L}w_b\cdot\tau_{l-1}\cdot x_{bl}.$$
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.9, (5a)

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_numIntervals
import Definitions.Def_AndOrSched_tau
open scoped Classical NNReal

namespace AndOrSched

/-- The objective (5a) of LP (5), `Σ_{b∈B} Σ_{l=1}^{L} w_b · τ_{l−1} · x_{bl}` (Happach, Schulz, arXiv:2001.07011v1, §2, p.9). -/
noncomputable def LP5Obj (I : Instance) (ε' : ℝ) (x : I.N → ℕ → ℝ) : ℝ :=
  ∑ b, (I.w (Sum.inr b) : ℝ) *
    ∑ l ∈ Finset.Icc 1 (numIntervals I ε'), tau ε' (l - 1) * x (Sum.inr b) l

end AndOrSched


