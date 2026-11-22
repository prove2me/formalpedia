-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.exists_threeAPFree_le_card_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:47.157801+00:00
-- url     : https://prove2.me/submissions/5fc69cbf-8cec-4494-ba1d-b92ced05e38c

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Combinatorics.Additive.AP.Three.Behrend
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Behrend

set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {P : ℕ} (hP : 0 < P) :
    ∃ S : Finset (ZMod P), ThreeAPFree (S : Set (ZMod P)) ∧ P / 2 * exp (-4 * √(log P)) ≤ #S := by
  obtain ⟨t, ht, hcard, hfree⟩ := rothNumberNat_spec ((P + 1) / 2)
  have hinj := CharP.natCast_injOn_Iio (ZMod P) P
  refine ⟨t.image Nat.cast, ?_, ?_⟩
  · push_cast
    refine hfree.image' (Nat.castAddMonoidHom (ZMod P)) (hinj.mono ?_)
    rintro _ ⟨a, ha, b, hb, rfl⟩
    grind [mem_range.1 (ht ha), mem_range.1 (ht hb)]
  · rw [card_image_of_injOn (hinj.mono fun a ha ↦ by grind [mem_range.1 (ht ha)]), hcard]
    grw [← Behrend.roth_lower_bound]
    rw [neg_mul, neg_mul]
    gcongr
    · rw [div_le_iff₀ two_pos]
      exact_mod_cast (by grind : P ≤ (P + 1) / 2 * 2)
    · exact_mod_cast (by grind : 0 < (P + 1) / 2)
    · exact_mod_cast (by grind : (P + 1) / 2 ≤ P)
end ArithmeticTriangleRemovalInVectorSpaces
