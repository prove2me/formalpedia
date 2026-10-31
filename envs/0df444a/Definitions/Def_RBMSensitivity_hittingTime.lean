-- Prove2me | Definitions.Def_RBMSensitivity_hittingTime
-- name    : RBMSensitivity_hittingTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:26.732996+00:00
-- url     : https://prove2.me/theorems/ca8724a2-4a4e-4e14-91f5-fe226271ab3e
-- title:
--   The hitting time of a set
-- statement:
--   The hitting time $\tau_A:=\inf\{t\ge 0:Z(t)\in A\}$ of a set $A$, with $\inf\emptyset=\infty$.
--
--   It is used to state positive recurrence.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 3.5, p.10

import Mathlib
import Definitions.Def_RBMSensitivity_E
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The hitting time `τ_A := inf{t ≥ 0 : Z(t) ∈ A}` of a set `A`, used for "positive
recurrent" in Theorem 3.5: arXiv:1907.00472v2, p.10.

**Formalization Note.** Values are in `ℝ≥0∞`, and the infimum of the empty set is `∞`, as on p.4. -/
noncomputable def hittingTime {J : ℕ} {Ω : Type*} (Z : ℝ≥0 → Ω → E J) (A : Set (E J)) (ω : Ω) :
    ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : Z t ω ∈ A), (t : ℝ≥0∞)

end RBMSensitivity


