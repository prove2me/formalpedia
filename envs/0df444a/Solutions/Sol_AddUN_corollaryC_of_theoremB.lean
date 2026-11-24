-- Prove2me | solution 1 for AddUN.corollaryC_of_theoremB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:36:01.182091+00:00
-- url     : https://prove2.me/submissions/f040c5de-499c-40f0-83cb-b475c23b2909

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
public import Theorems.Thm_AddUN_univ_notMem_null
public import Theorems.Thm_IdealInvariant_non_le_cof
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_mono


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution (hB : TheoremB) (ha : CorollaryA) (hb : CorollaryB) :
    CorollaryC := by
  intro h
  refine ⟨?_, ?_, fun A hA ↦ ?_⟩
  · rw [show (3 : Ordinal) = 2 + 1 by norm_num, ← succ_aleph, Order.succ_le_iff]
    exact not_le.1 fun hc ↦ h.ne' (hb hc)
  · exact (non_le_cof univ_notMem_null).lt_of_ne fun hnc ↦ h.ne' (ha hnc)
  · by_contra hc
    obtain ⟨B, hBA, hBcard⟩ := le_mk_iff_exists_subset.1 (not_lt.1 hc)
    exact h.ne' (hB B (hA.mono hBA) hBcard)
end AddUN
