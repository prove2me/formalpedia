-- Prove2me | solution 1 for AddUN.aleph0_lt_add_universallyNull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:36:21.904713+00:00
-- url     : https://prove2.me/submissions/3e6c2e71-8ef3-42fc-a694-2a8ad042216e

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
public import Theorems.Thm_MeasureTheory_aleph0_lt_add_universallyNullSets
public import Theorems.Thm_MeasureTheory_not_isUniversallyNull_univ_cantor


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution : ℵ₀ < add 𝒰𝒩 :=
  aleph0_lt_add_universallyNullSets not_isUniversallyNull_univ_cantor
end AddUN
