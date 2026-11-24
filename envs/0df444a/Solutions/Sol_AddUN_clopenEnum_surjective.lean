-- Prove2me | solution 1 for AddUN.clopenEnum_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:40:26.571402+00:00
-- url     : https://prove2.me/submissions/db205581-7bb0-43d4-9d85-294ce9f809fd

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_Uniformity
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_AddUN_Grzegorek

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution : Function.Surjective clopenEnum :=
  (exists_surjective_nat (Clopens (ℕ → Bool))).choose_spec
end AddUN
