-- Prove2me | solution 1 for AddUN.isUniversallyNull_of_mk_lt_non_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:46:01.274829+00:00
-- url     : https://prove2.me/submissions/405fe51e-1655-4dc2-b94b-164864a5929d

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_Uniformity
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_AddUN_Grzegorek
public import Theorems.Thm_AddUN_isUniversallyNull_of_mk_lt_non
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_of_injOn


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution {Z : Type} [MeasurableSpace Z]
    {j : Z → ℕ → Bool} (hj : Measurable j) (hinj : Function.Injective j) {A : Set Z}
    (hA : #A < non 𝒩) : IsUniversallyNull A :=
  (isUniversallyNull_of_mk_lt_non (mk_image_le.trans_lt hA)).of_injOn hj hinj.injOn Subset.rfl
end AddUN
