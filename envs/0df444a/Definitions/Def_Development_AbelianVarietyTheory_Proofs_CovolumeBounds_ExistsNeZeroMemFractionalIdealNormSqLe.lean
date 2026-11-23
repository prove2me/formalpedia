-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:28.913938+00:00
-- url     : https://prove2.me/theorems/1a84cfb2-066a-464f-9e47-47f195720d32
-- title:
--   Exists Ne Zero Mem Fractional Ideal Norm Sq Le
-- statement:
--   Definitions and structural lemmas for Exists Ne Zero Mem Fractional Ideal Norm Sq Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroMemFractionalIdealNormSqLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped nonZeroDivisors NNReal ENNReal
section General
variable (K : Type*) [Field K] [NumberField K]
end General
section TotallyComplex
variable {E : Type*} [Field E] [NumberField E] [IsTotallyComplex E] {f : ℕ}
end TotallyComplex
end GlobalTheory


