-- Prove2me | solution 1 for AddUN.add_universallyNull_le_add_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:44:27.519191+00:00
-- url     : https://prove2.me/submissions/ab2eaf3e-f7e2-490e-9a1e-6300f0f508a3

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
public import Theorems.Thm_AddUN_add_universallyNull_le_add_null_of_codingLemma
public import Theorems.Thm_AddUN_codingLemma


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN
namespace AddUN
theorem _root_.solution (A : Set (ℕ → Bool)) (hA : IsUniversallyNull A)
    (hcard : #A = cof 𝒩) : add 𝒰𝒩 ≤ add 𝒩 :=
  add_universallyNull_le_add_null_of_codingLemma codingLemma A hA hcard
end AddUN
