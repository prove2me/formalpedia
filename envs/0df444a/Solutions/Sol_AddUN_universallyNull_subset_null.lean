-- Prove2me | solution 1 for AddUN.universallyNull_subset_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:35:03.986232+00:00
-- url     : https://prove2.me/submissions/274baa89-5f32-4745-936a-39b29ae62fa6

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
public import Theorems.Thm_MeasureTheory_universallyNullSets_subset_nullSets


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution : 𝒰𝒩 ⊆ 𝒩 :=
  universallyNullSets_subset_nullSets cantorMeasure
end AddUN
