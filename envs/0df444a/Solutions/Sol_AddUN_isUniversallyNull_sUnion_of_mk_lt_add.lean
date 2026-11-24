-- Prove2me | solution 1 for AddUN.isUniversallyNull_sUnion_of_mk_lt_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:45:03.085884+00:00
-- url     : https://prove2.me/submissions/648fa318-3f0c-437b-87c4-380300b1091e

module
public import Definitions.Def_AddUN_Coding
public import Definitions.Def_AddUN_Additivity
public import Theorems.Thm_AddUN_measure_sUnion_null_of_mk_lt_add

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN
open Coding
namespace AddUN
theorem _root_.solution {𝒜 : Set (Set (ℕ → Bool))}
    (h𝒜 : ∀ A ∈ 𝒜, IsUniversallyNull A) (hcard : #𝒜 < add 𝒩) : IsUniversallyNull (⋃₀ 𝒜) :=
  fun μ _ _ ↦ measure_sUnion_null_of_mk_lt_add μ (fun A hA ↦ h𝒜 A hA μ) hcard
end AddUN
