-- Prove2me | solution 1 for AddUN.Coding.finite_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:40:59.05669+00:00
-- url     : https://prove2.me/submissions/be822e58-acee-406c-b5da-7792e10ca8ec

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_card_le_of_subset_bad

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution {K : Set (ℕ → Bool)} (hK : MeasurableSet K) (c : ℕ → Bool) (n : ℕ) :
    (bad K c n).Finite := by
  by_contra hinf
  obtain ⟨J, hJ, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (2 ^ (3 * mu n + n) + 1)
  have := card_le_of_subset_bad hK J hJ
  omega
end AddUN.Coding
