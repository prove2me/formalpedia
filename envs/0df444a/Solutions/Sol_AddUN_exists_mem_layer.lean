-- Prove2me | solution 1 for AddUN.exists_mem_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:42:14.901912+00:00
-- url     : https://prove2.me/submissions/7c22fe00-0737-402e-a3f8-cf463a3f66f7

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
public import Theorems.Thm_AddUN_inner_mono
public import Theorems.Thm_AddUN_iUnion_inner
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
theorem _root_.solution (hU : IsOpen U) {M : ℕ → ℕ} (hM : StrictMono M) {y : ℕ → Bool}
    (hy : y ∈ U) : ∃ k, y ∈ layer U M k := by
  classical
  have hex : ∃ k, y ∈ inner U (M k) := by
    rw [← iUnion_inner hU] at hy
    obtain ⟨n, hn⟩ := mem_iUnion.1 hy
    exact ⟨n, inner_mono hM.le_apply hn⟩
  refine ⟨Nat.find hex, ?_⟩
  cases hk : Nat.find hex with
  | zero => simpa [layer, hk] using Nat.find_spec hex
  | succ k =>
    refine ⟨by simpa [hk] using Nat.find_spec hex, ?_⟩
    exact Nat.find_min hex (by omega)
end AddUN
