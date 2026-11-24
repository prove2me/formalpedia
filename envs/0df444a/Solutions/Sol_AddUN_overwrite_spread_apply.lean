-- Prove2me | solution 1 for AddUN.overwrite_spread_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:42:50.817795+00:00
-- url     : https://prove2.me/submissions/65fd36f8-acc7-4ad1-bb3e-2e1adfb8eba2

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_length_revPrefix
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip
attribute [local simp] MeasureTheory.length_revPrefix



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}
namespace AddUN
theorem _root_.solution (g : ℕ → ℕ) (k₀ : ℕ) (c u : ℕ → Bool) (n : ℕ) :
    overwrite (spread g k₀) c u (spread g k₀ n) = c n := by
  simp [overwrite, spread]
end AddUN
