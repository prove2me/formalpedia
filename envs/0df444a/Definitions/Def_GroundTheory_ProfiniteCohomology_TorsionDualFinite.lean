-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
-- name    : GroundTheory_ProfiniteCohomology_TorsionDualFinite
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:07:52.017182+00:00
-- url     : https://prove2.me/theorems/0764e195-fd2c-544a-af1b-79e733886136
-- title:
--   Torsion Dual Finite
-- statement:
--   Definitions and structural lemmas for Torsion Dual Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
import Theorems.Thm_GroundTheory_ProfCoh_QZDual_eval_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZ_mk_eq_zero_iff
import Theorems.Thm_GroundTheory_ProfCoh_QZ_mk_surjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.QZDual.eval_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open Function
namespace QZ
noncomputable def toReal : QZ →+ AddCircle (1 : ℝ) :=
  (QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ)) (AddSubgroup.zmultiples (1 : ℝ))
    (Rat.castHom ℝ).toAddMonoidHom (by
      rw [AddSubgroup.zmultiples_le]
      exact ⟨1, by simp⟩)).comp toAddCircle.toAddMonoidHom
theorem toReal_mk (q : ℚ) : toReal (mk q) = ((q : ℝ) : AddCircle (1 : ℝ)) :=
  rfl
theorem toReal_injective : Injective toReal := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨q, rfl⟩ := mk_surjective x
  rw [toReal_mk, AddCircle.coe_eq_zero_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [mk_eq_zero_iff]
  refine ⟨n, ?_⟩
  have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
  exact_mod_cast this
noncomputable def toComplex (x : QZ) : ℂ :=
  (AddCircle.toCircle (toReal x) : ℂ)
theorem toComplex_injective : Injective toComplex := fun _ _ h =>
  toReal_injective (AddCircle.injective_toCircle one_ne_zero (Circle.ext h))
@[simp]
theorem toComplex_zero : toComplex 0 = 1 := by
  simp [toComplex]
theorem toComplex_add (x y : QZ) : toComplex (x + y) = toComplex x * toComplex y := by
  simp [toComplex, AddCircle.toCircle_add]
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
noncomputable def toAddChar (f : G →+ QZ) : AddChar G ℂ where
  toFun g := toComplex (f g)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [toComplex_add]
@[simp]
theorem toAddChar_apply (f : G →+ QZ) (g : G) : toAddChar f g = toComplex (f g) :=
  rfl
theorem toAddChar_injective : Injective (toAddChar (G := G)) := fun _ _ h =>
  AddMonoidHom.ext fun a => toComplex_injective (DFunLike.congr_fun h a)
theorem toAddChar_add (f f' : G →+ QZ) : toAddChar (f + f') = toAddChar f + toAddChar f' := by
  ext a
  simp [toComplex_add]
theorem exists_apply_ne_zero {a : G} (ha : a ≠ 0) : ∃ f : G →+ QZ, f a ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  refine ⟨toAddCircle.symm.toAddMonoidHom.comp (c : G →+ AddCircle (1 : ℚ)), fun h => hc ?_⟩
  exact (AddEquiv.map_eq_zero_iff toAddCircle.symm).mp h
variable (G) in

def evalHom : G →+ ((G →+ QZ) →+ QZ) where
  toFun a :=
    { toFun := fun f => f a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_zero' := by ext f; simp
  map_add' a b := by ext f; simp
theorem evalHom_injective : Injective (evalHom G) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨f, hf⟩ := exists_apply_ne_zero hne
  exact hf (DFunLike.congr_fun ha f)
instance [Finite G] : Finite (G →+ QZ) :=
  Finite.of_injective _ toAddChar_injective
theorem card_hom_le [Finite G] : Nat.card (G →+ QZ) ≤ Nat.card G := by
  have := Fintype.ofFinite G
  calc Nat.card (G →+ QZ) ≤ Nat.card (AddChar G ℂ) :=
        Nat.card_le_card_of_injective _ toAddChar_injective
    _ ≤ Nat.card G := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact AddChar.card_addChar_le G ℂ
theorem card_hom [Finite G] : Nat.card (G →+ QZ) = Nat.card G :=
  card_hom_le.antisymm <| (Nat.card_le_card_of_injective _ evalHom_injective).trans card_hom_le
variable (G) in

noncomputable def addCharEquiv [Finite G] : (G →+ QZ) ≃+ AddChar G ℂ :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' toAddChar toAddChar_add)
    (by
      have := Fintype.ofFinite G
      refine toAddChar_injective.bijective_of_nat_card_le ?_
      rw [card_hom, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq])
end QZ
namespace QZDual
variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
noncomputable def addCharEquiv [Finite N] : QZDual N ≃+ AddChar N ℂ :=
  toAddMonoidHomEquiv.trans (QZ.addCharEquiv N)
instance [Finite N] : Finite (QZDual N) :=
  Finite.of_injective _ (toAddMonoidHomEquiv (A := N)).injective
end QZDual
end GroundTheory.ProfCoh


