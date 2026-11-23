-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableAvgS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableAvgS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:38.243391+00:00
-- url     : https://prove2.me/theorems/0716ead8-612d-43ba-9df7-785ebab39283
-- title:
--   Measurable Avg S
-- statement:
--   Definitions and structural lemmas for Measurable Avg S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableAvgS.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal NNReal
noncomputable section
namespace PI.QuotInvW
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
def avgS (μS : Measure (MtM m)) (f : MtM m → ℝ≥0∞) (x : MtM m) : ℝ≥0∞ := ∫⁻ s, f (mm s x) ∂μS
end PI.QuotInvW


