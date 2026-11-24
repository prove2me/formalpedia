-- Prove2me | solution 1 for AddUN.corollaryB_of_corollaryA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:58.412808+00:00
-- url     : https://prove2.me/submissions/2192618b-fffd-40f6-a96f-4ae7028fa0c6

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
public import Theorems.Thm_AddUN_univ_notMem_null
public import Theorems.Thm_AddUN_aleph0_lt_add_null
public import Theorems.Thm_AddUN_add_universallyNull_le_non_null
public import Theorems.Thm_IdealInvariant_non_le_cof
public import Theorems.Thm_MeasureTheory_cof_nullSets_le_continuum


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution (ha : CorollaryA) (hle : GotoCor513) : CorollaryB := by
  intro h
  by_cases hnc : non 𝒩 = cof 𝒩
  · exact ha hnc
  have h1 : non 𝒩 < ℵ_ 2 := ((non_le_cof univ_notMem_null).lt_of_ne hnc).trans_le
    ((cof_nullSets_le_continuum cantorMeasure).trans h)
  have h2 : non 𝒩 ≤ ℵ₁ := by
    rwa [← one_add_one_eq_two, ← succ_aleph, Order.lt_succ_iff] at h1
  have h4 : ℵ₁ ≤ add 𝒩 := aleph_one_le_iff.2 aleph0_lt_add_null
  exact le_antisymm (add_universallyNull_le_non_null.trans (h2.trans h4)) hle
end AddUN
