-- Prove2me | Definitions.Def_RBMSensitivity_IsStationaryLaw
-- name    : RBMSensitivity_IsStationaryLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:41.123295+00:00
-- url     : https://prove2.me/theorems/94018cf0-1cfe-49d2-afa2-80e88b1c43ed
-- title:
--   A stationary distribution of a Markov semigroup
-- statement:
--   A probability measure $\mu$ is a **stationary distribution** of $\{\mathcal P_t\}$ if $\mu\mathcal P_t=\mu$ for all $t\ge 0$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 8.1, p.33

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `μ` is a stationary distribution of the semigroup `Pt`: arXiv:1907.00472v2, Theorem 8.1, p.33. -/
def IsStationaryLaw {S : Type*} [MeasurableSpace S] (Pt : ℝ≥0 → Kernel S S) (μ : Measure S) :
    Prop :=
  IsProbabilityMeasure μ ∧ ∀ t, μ.bind (Pt t) = μ

end RBMSensitivity


