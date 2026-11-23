-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:12.853705+00:00
-- url     : https://prove2.me/theorems/e4c997b1-396e-425f-a7bd-47659258319f
-- title:
--   Unit Trace Unramified Extension
-- statement:
--   Definitions and structural lemmas for Unit Trace Unramified Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitTraceUnramifiedExtension.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_int_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
def intMap (hU : IsUnrExt K K' d φ) : K.O →+* K'.O where
  toFun a := Classical.choose (exists_int_image hU a)
  map_one' := IsFractionRing.injective K'.O K'.E (by
    rw [Classical.choose_spec (exists_int_image hU 1)]; simp)
  map_mul' a b := IsFractionRing.injective K'.O K'.E (by
    have h1 := Classical.choose_spec (exists_int_image hU (a * b))
    have h2 := Classical.choose_spec (exists_int_image hU a)
    have h3 := Classical.choose_spec (exists_int_image hU b)
    rw [h1]; simp only [map_mul, h2, h3])
  map_zero' := IsFractionRing.injective K'.O K'.E (by
    rw [Classical.choose_spec (exists_int_image hU 0)]; simp)
  map_add' a b := IsFractionRing.injective K'.O K'.E (by
    have h1 := Classical.choose_spec (exists_int_image hU (a + b))
    have h2 := Classical.choose_spec (exists_int_image hU a)
    have h3 := Classical.choose_spec (exists_int_image hU b)
    rw [h1]; simp only [map_add, h2, h3])
end GlobalTheory.UnitLemma.Unr


