-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDoma
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDoma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:47.591725+00:00
-- url     : https://prove2.me/theorems/a7c59ae6-f416-4fa1-a375-fa877982ad9c
-- title:
--   Adic Completion Valuation Ring Complete Valuation Doma
-- statement:
--   Definitions and structural lemmas for Adic Completion Valuation Ring Complete Valuation Doma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionValuationRingCompleteValuationDoma.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
namespace GlobalTheory.ValCompletion
section General
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}
end General
section Val
variable {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {x : V}
end Val
end GlobalTheory.ValCompletion


