-- Prove2me | Definitions.Def_LocalDOvS_SUS_IsValidAlg
-- name    : LocalDOvS_SUS_IsValidAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:48.953175+00:00
-- url     : https://prove2.me/theorems/ab51b79c-e9bd-4ecc-9f50-4033b6f1bb0a
-- title:
--   Algorithm on the decision space $[N]$
-- statement:
--   A sequential algorithm **acts on** $X=[N]$ if every decision it simulates or returns, after any history, lies in $[N]=\{1,\dots,N\}$.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Assumption 3, p.10

import Mathlib
import Definitions.Def_LocalDOvS_SUS_SeqAlg

namespace LocalDOvS.SUS

/-- A sequential algorithm for the decision space `X = [N] = {1, …, N}` (Zhang–Zheng–Lavaei,
arXiv:2012.02427v2, Assumption 3, p.10, with `d = 1`): every decision it simulates or returns,
after any history, lies in `[N]`. -/
def IsValidAlg (N : ℕ) (A : SeqAlg) : Prop :=
  ∀ (h : List (ℕ × ℝ)) (x : ℕ), (A h = Step.sample x ∨ A h = Step.stop x) → x ∈ Finset.Icc 1 N

end LocalDOvS.SUS


