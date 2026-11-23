-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:07.849674+00:00
-- url     : https://prove2.me/theorems/d7140361-b038-40cb-9cea-10442dc7d711
-- title:
--   Norm Le Of Complete Homogeneous Le
-- statement:
--   Definitions and structural lemmas for Norm Le Of Complete Homogeneous Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormLeOfCompleteHomogeneousLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
namespace GlobalTheory.CompleteHomogeneousBound
def WeightedSummable (r : ℝ) (f : ℂ⟦X⟧) : Prop :=
  Summable fun m : ℕ => ‖coeff m f * (r : ℂ) ^ m‖
end GlobalTheory.CompleteHomogeneousBound


