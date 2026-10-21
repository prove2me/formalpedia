-- Prove2me | Definitions.Def_MazurTransfer_OriginalSchemePointNaturalEquivalenceIsoData20261020
-- name    : MazurTransfer_OriginalSchemePointNaturalEquivalenceIsoData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T01:22:53.153276+00:00
-- url     : https://prove2.me/theorems/53c23d8f-ef7e-4fd4-8752-b03f996b7019
-- title:
--   Original scheme and over-base isomorphism from a natural point equivalence
-- statement:
--   Retain the original forward and backward points, intrinsic inverse naturality and inverse-composition certificates, and both exact original isomorphism values over the same base. All seven complete original types, four whole data values and all generated structural certificates are independently checked. The given point-map proposition is a separate theorem interface. Named downstream consumer: the principal-action scheme isomorphism of the actual integral norm-preimage torsor at nineteen.
-- source:
--   MazurTheorem SchemePointNaturalEquivalenceIso by Vas and contributors; complete original constructor types and whole values, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a natural equivalence on ALL scheme-valued points induces
an isomorphism over the SAME base, retaining the given point map.
Named downstream consumer: principal-action scheme isomorphism of the
actual integral norm-preimage torsor at nineteen.
-/
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

noncomputable section
namespace MazurTransfer.SchemePointNaturalEquivalenceIso
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u
variable {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
variable (e : ∀ {T : Scheme.{u}} (t : T ⟶ B), SchemeHomOver t f ≃ SchemeHomOver t g)
variable (hNat : ∀ {T T' : Scheme.{u}} (t : T ⟶ B) (t' : T' ⟶ B)
  (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f),
  e t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
    GoodReductionJacobian.schemeHomOverComp ψ hψ (e t x))

include hNat in
theorem symm_natural {T T' : Scheme.{u}} (t : T ⟶ B) (t' : T' ⟶ B)
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (y : SchemeHomOver t g) :
    (e t').symm (GoodReductionJacobian.schemeHomOverComp ψ hψ y) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ ((e t).symm y) := by
  apply (e t').injective
  rw [Equiv.apply_symm_apply, hNat, Equiv.apply_symm_apply]

def forwardPoint : SchemeHomOver f g := e f ⟨𝟙 X, Category.id_comp f⟩
def backwardPoint : SchemeHomOver g f := (e g).symm ⟨𝟙 Y, Category.id_comp g⟩

include hNat in
theorem forward_backward : (forwardPoint f g e).val ≫ (backwardPoint f g e).val = 𝟙 X := by
  have h := symm_natural f g e hNat g f (forwardPoint f g e).val
    (forwardPoint f g e).property (⟨𝟙 Y, Category.id_comp g⟩ : SchemeHomOver g g)
  have he : GoodReductionJacobian.schemeHomOverComp (forwardPoint f g e).val
      (forwardPoint f g e).property (⟨𝟙 Y, Category.id_comp g⟩ : SchemeHomOver g g) =
        forwardPoint f g e := Subtype.ext (Category.comp_id _)
  rw [he] at h
  have hh : (e f).symm (forwardPoint f g e) =
      (⟨𝟙 X, Category.id_comp f⟩ : SchemeHomOver f f) := (e f).symm_apply_apply _
  rw [hh] at h
  exact (congrArg Subtype.val h).symm

include hNat in
theorem backward_forward : (backwardPoint f g e).val ≫ (forwardPoint f g e).val = 𝟙 Y := by
  have h := hNat f g (backwardPoint f g e).val
    (backwardPoint f g e).property (⟨𝟙 X, Category.id_comp f⟩ : SchemeHomOver f f)
  have he : GoodReductionJacobian.schemeHomOverComp (backwardPoint f g e).val
      (backwardPoint f g e).property (⟨𝟙 X, Category.id_comp f⟩ : SchemeHomOver f f) =
        backwardPoint f g e := Subtype.ext (Category.comp_id _)
  rw [he] at h
  have hh : e g (backwardPoint f g e) =
      (⟨𝟙 Y, Category.id_comp g⟩ : SchemeHomOver g g) := (e g).apply_symm_apply _
  rw [hh] at h
  exact (congrArg Subtype.val h).symm

include hNat in
def schemeIso : X ≅ Y where
  hom := (forwardPoint f g e).val
  inv := (backwardPoint f g e).val
  hom_inv_id := forward_backward f g e hNat
  inv_hom_id := backward_forward f g e hNat

include hNat in
def overIso : Over.mk f ≅ Over.mk g where
  hom := Over.homMk (schemeIso f g e hNat).hom (forwardPoint f g e).property
  inv := Over.homMk (schemeIso f g e hNat).inv (backwardPoint f g e).property
  hom_inv_id := Over.OverMorphism.ext ((schemeIso f g e hNat).hom_inv_id)
  inv_hom_id := Over.OverMorphism.ext ((schemeIso f g e hNat).inv_hom_id)



end MazurTransfer.SchemePointNaturalEquivalenceIso
#print axioms MazurTransfer.SchemePointNaturalEquivalenceIso.symm_natural
#print axioms MazurTransfer.SchemePointNaturalEquivalenceIso.forwardPoint
#print axioms MazurTransfer.SchemePointNaturalEquivalenceIso.backwardPoint
#print axioms MazurTransfer.SchemePointNaturalEquivalenceIso.forward_backward
#print axioms MazurTransfer.SchemePointNaturalEquivalenceIso.backward_forward
#print axioms MazurTransfer.SchemePointNaturalEquivalenceIso.schemeIso
#print axioms MazurTransfer.SchemePointNaturalEquivalenceIso.overIso


