-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti
-- name    : Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:02.03642+00:00
-- url     : https://prove2.me/theorems/9fa73d85-d746-4b11-968b-a5c1031b1e93
-- title:
--   Low KAdd Strict Anti
-- statement:
--   Definitions and structural lemmas for Low KAdd Strict Anti, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace
namespace GlobalTheory.DiscreteSeriesTest
def chi (m : ℤ) (g : Matrix (Fin 1) (Fin 1) ℂ) : ℂ →L[ℂ] ℂ := (g 0 0) ^ m • ContinuousLinearMap.id ℂ ℂ
end GlobalTheory.DiscreteSeriesTest


