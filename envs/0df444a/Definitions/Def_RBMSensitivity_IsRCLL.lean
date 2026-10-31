-- Prove2me | Definitions.Def_RBMSensitivity_IsRCLL
-- name    : RBMSensitivity_IsRCLL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:40.11025+00:00
-- url     : https://prove2.me/theorems/e09c4adb-0eb7-45c0-a83c-8fcf4dbd341d
-- title:
--   Right continuous paths with left limits
-- statement:
--   A path $\zeta:[0,\infty)\to S$ is **RCLL** if it is right continuous and has finite left limits. These are the elements of $\mathbb D(S)$.
--
--   Derivative processes are RCLL and need not be continuous, which is why this class of paths appears alongside the continuous RBM.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §1.4, p.4

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- A path is RCLL (right continuous with finite left limits): arXiv:1907.00472v2, §1.4, p.4.

**Formalization Note.** Time is `ℝ≥0`. At `t = 0` the left filter is trivial, so the left-limit
clause holds there automatically. -/
def IsRCLL {S : Type*} [TopologicalSpace S] (ζ : ℝ≥0 → S) : Prop :=
  ∀ t, ContinuousWithinAt ζ (Set.Ioi t) t ∧ ∃ l, Tendsto ζ (𝓝[<] t) (𝓝 l)

end RBMSensitivity


