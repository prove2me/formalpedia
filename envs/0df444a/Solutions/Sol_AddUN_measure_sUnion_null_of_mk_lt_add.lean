-- Prove2me | solution 1 for AddUN.measure_sUnion_null_of_mk_lt_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:44:15.756426+00:00
-- url     : https://prove2.me/submissions/92fbd488-ca50-40d7-a94f-457375dd42d9

module
public import Definitions.Def_AddUN_Coding
public import Definitions.Def_AddUN_Additivity
public import Theorems.Thm_AddUN_exists_localising_slalom
public import Theorems.Thm_AddUN_measure_sUnion_null_of_localised


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN
open Coding
namespace AddUN
theorem _root_.solution (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ]
    {𝒢 : Set (Set (ℕ → Bool))} (h𝒢 : ∀ G ∈ 𝒢, μ G = 0) (hcard : #𝒢 < add 𝒩) :
    μ (⋃₀ 𝒢) = 0 :=
  measure_sUnion_null_of_localised μ (fun n ↦ 2 ^ (3 * mu n + n)) h𝒢 fun _ hF ↦
    exists_localising_slalom (hF.trans_lt hcard)
end AddUN
