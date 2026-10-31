-- Prove2me | Definitions.Def_GeomRescale_IsRun
-- name    : GeomRescale_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:07.760998+00:00
-- url     : https://prove2.me/theorems/e87ee7ee-b43d-442b-b07d-3451e21847ac
-- title:
--   Runs of Algorithm 2
-- statement:
--   A run on input $f, \Lambda$ is a finite list of states that begins with the initial state and in which consecutive states are related by a step. A uniform bound on the length of runs rules out infinite runs.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10

import Mathlib
import Definitions.Def_GeomRescale_init
import Definitions.Def_GeomRescale_Step

namespace GeomRescale

/-- `l` is a finite run of Algorithm Rescaling-SFM on input `f`, `Λ` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10): it
begins with the initial state and consecutive states are related by `Step`. -/
def IsRun {n : ℕ} (f : Finset (Fin n) → ℤ) (Λ : ℝ) (l : List (St n)) : Prop :=
  (∃ t, l = init n :: t) ∧ l.IsChain (Step f Λ)

end GeomRescale


