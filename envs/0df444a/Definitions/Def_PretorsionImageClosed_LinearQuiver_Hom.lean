-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
-- name    : PretorsionImageClosed_LinearQuiver_Hom
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:17:58.813963+00:00
-- url     : https://prove2.me/theorems/ac217289-fa4c-4e56-a55c-f9fd9af0c075
-- title:
--   Hom
-- statement:
--   Definitions and structural lemmas for Hom, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_epi_iff_surjective
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_mono_iff_injective
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSpace_of_mem

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits
namespace LinearQuiver
universe u
variable (k : Type u) [Field k] {n : ℕ}
def unit (c d i : Fin n) : intervalSpace k c d i :=
  ⟨if c ≤ i ∧ i ≤ d then 1 else 0, by
    unfold intervalSpace
    split_ifs
    · exact Submodule.mem_top
    · exact Submodule.zero_mem _⟩
variable {k}
def coord {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (i : Fin n) : k :=
  ((η.app i).hom.hom (unit k c d i)).1
theorem coe_inclusionOrZero_intervalSpace {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) (i : Fin n)
    (x : intervalSpace k c d i) :
    ((inclusionOrZero k (intervalSpace k c d i) (intervalSpace k a b i) x : intervalSpace k a b i) : k) =
      if i ≤ b then (x : k) else 0 := by
  rw [coe_inclusionOrZero]
  by_cases hi : c ≤ i ∧ i ≤ d
  · by_cases hib : i ≤ b
    · rw [if_pos hib, if_pos]
      unfold intervalSpace
      rw [if_pos hi, if_pos ⟨hac.trans hi.1, hib⟩]
    · rw [if_neg hib, if_neg]
      unfold intervalSpace
      rw [if_pos hi, if_neg (fun h => hib h.2)]
      intro hle
      have := hle (Submodule.mem_top (x := (1 : k)))
      rw [Submodule.mem_bot] at this
      exact one_ne_zero this
  · rw [coe_eq_zero_of_not_mem k hi x]
    split_ifs <;> rfl
def canonicalHom {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) : interval k c d ⟶ interval k a b where
  app i := FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k c d i) (intervalSpace k a b i))
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun (x : intervalSpace k c d i) => ?_
    apply Subtype.ext
    change ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a b j) : k) =
      ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a b j) : k)
    rw [coe_inclusionOrZero_intervalSpace hac hbd, coe_intervalMap k (leOfHom f),
      coe_intervalMap k (leOfHom f), coe_inclusionOrZero_intervalSpace hac hbd]
    by_cases hjb : j ≤ b
    · rw [if_pos hjb, if_pos hjb, if_pos (hjb.trans hbd), if_pos ((leOfHom f).trans hjb)]
    · rw [if_neg hjb, if_neg hjb]
instance mono_intervalIncl {a ℓ d : Fin n} (h : a ≤ ℓ) : Mono (intervalIncl k d h) := by
  rw [NatTrans.mono_iff_mono_app]
  intro i
  rw [FGModuleCat.mono_iff_injective]
  intro (x : intervalSpace k ℓ d i) (y : intervalSpace k ℓ d i) hxy
  apply Subtype.ext
  have := congrArg Subtype.val hxy
  change ((inclusionOrZero k _ _ x : intervalSpace k a d i) : k) =
    ((inclusionOrZero k _ _ y : intervalSpace k a d i) : k) at this
  rwa [coe_inclusionOrZero_left k h, coe_inclusionOrZero_left k h] at this
instance epi_intervalProj (a : Fin n) {ℓ d : Fin n} (h : ℓ ≤ d) : Epi (intervalProj k a h) := by
  rw [NatTrans.epi_iff_epi_app]
  intro i
  rw [FGModuleCat.epi_iff_surjective]
  intro (y : intervalSpace k a ℓ i)
  by_cases hi : a ≤ i ∧ i ≤ ℓ
  · refine ⟨⟨y.1, ?_⟩, ?_⟩
    · rw [intervalSpace_of_mem k ⟨hi.1, hi.2.trans h⟩]
      exact Submodule.mem_top
    · apply Subtype.ext
      change ((inclusionOrZero k _ _ (⟨y.1, _⟩ : intervalSpace k a d i) : intervalSpace k a ℓ i) : k) = _
      rw [coe_inclusionOrZero_right k h, if_pos hi.2]
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    erw [map_zero]
    rw [coe_eq_zero_of_not_mem k hi y]
    rfl
end LinearQuiver
end PretorsionImageClosed


