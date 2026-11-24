-- Prove2me | solution 1 for AddUN.determined_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:42:06.850411+00:00
-- url     : https://prove2.me/submissions/bd2d1fe5-0be7-4d62-8742-9b1f9a0efc1f

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
public import Theorems.Thm_AddUN_determined_inner
public import Theorems.Thm_MeasureTheory_Determined_diff
public import Theorems.Thm_MeasureTheory_Determined_mono
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_mono


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}
namespace AddUN
theorem _root_.solution {M : ℕ → ℕ} (hM : Monotone M) (k : ℕ) :
    Determined (↑(Finset.range (M k))) (layer U M k) := by
  cases k with
  | zero => exact determined_inner _
  | succ k =>
    exact (determined_inner _).diff ((determined_inner _).mono
      (Finset.coe_subset.2 (Finset.range_subset_range.2 (hM (Nat.le_succ k)))))
end AddUN
