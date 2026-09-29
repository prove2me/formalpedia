-- Prove2me | solution 1 for AlgebraicGeometry.IsPullback.surjective_residueFieldMap_of_isIso_residueFieldMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/efbfce99-41f1-5612-8af3-fa194d72b6ae

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsPullback_surjective_residueFieldMap_of_isIso_residueFieldMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {P X T S : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (H : IsPullback fst snd f g) (t : ↥P) [IsIso (f.residueFieldMap (fst.base t))] :
    Function.Surjective (snd.residueFieldMap t).hom := by
  classical

  let e := H.isoPullback
  let t₀ : ↥(pullback f g) := e.hom.base t
  have hfst : (pullback.fst f g).base t₀ = fst.base t := by
    show (e.hom ≫ pullback.fst f g).base t = _
    rw [H.isoPullback_hom_fst]
  have hsnd : snd = e.hom ≫ pullback.snd f g := (H.isoPullback_hom_snd).symm
  haveI hiso : IsIso (f.residueFieldMap ((pullback.fst f g).base t₀)) := by rw [hfst]; infer_instance

  suffices key : Function.Surjective ((pullback.snd f g).residueFieldMap t₀).hom by
    rw [hsnd, Scheme.residueFieldMap_comp]
    show Function.Surjective ((e.hom.residueFieldMap t).hom.comp ((pullback.snd f g).residueFieldMap t₀).hom)
    haveI : IsIso (e.hom.residueFieldMap t) := inferInstance
    exact ((ConcreteCategory.bijective_of_isIso (e.hom.residueFieldMap t)).2).comp key

  let T₀ := Scheme.Pullback.Triplet.ofPoint t₀
  haveI : IsIso (f.residueFieldMap T₀.x) := hiso
  haveI : IsIso ((S.residueFieldCongr T₀.hx).inv ≫ f.residueFieldMap T₀.x) := inferInstance
  haveI hinr : IsIso T₀.tensorInr := by
    show IsIso (pushout.inr _ _)
    infer_instance

  let ρ : T.residueField T₀.y ⟶ (pullback f g).residueField t₀ := T₀.tensorInr ≫ Scheme.Pullback.ofPointTensor t₀
  have hρ : ρ = (pullback.snd f g).residueFieldMap t₀ := pushout.inr_desc _ _ _
  rw [← hρ]
  let u : Spec (T.residueField T₀.y) ⟶ pullback f g := Spec.map (inv T₀.tensorInr) ≫ T₀.SpecTensorTo
  have h1 : Spec.map ρ = Spec.map (Scheme.Pullback.ofPointTensor t₀) ≫ Spec.map T₀.tensorInr := Spec.map_comp _ _
  have h2 : Spec.map T₀.tensorInr ≫ Spec.map (inv T₀.tensorInr) = 𝟙 _ := by
    have h := congrArg Spec.map (IsIso.inv_hom_id T₀.tensorInr)
    have h' : Spec.map (inv T₀.tensorInr ≫ T₀.tensorInr) = Spec.map T₀.tensorInr ≫ Spec.map (inv T₀.tensorInr) :=
      Spec.map_comp _ _
    rw [← h', h]
    exact Spec.map_id _
  have hu : Spec.map ρ ≫ u = (pullback f g).fromSpecResidueField t₀ := by
    show Spec.map ρ ≫ (Spec.map (inv T₀.tensorInr) ≫ T₀.SpecTensorTo) = _
    rw [h1, Category.assoc, ← Category.assoc (Spec.map T₀.tensorInr), h2, Category.id_comp]
    exact Scheme.Pullback.ofPointTensor_SpecTensorTo t₀

  obtain ⟨⟨t', ψ⟩, hψ⟩ : ∃ q : Σ x : ↥(pullback f g), (pullback f g).residueField x ⟶ CommRingCat.of (T.residueField T₀.y),
      Spec.map q.2 ≫ (pullback f g).fromSpecResidueField q.1 = u :=
    ⟨Scheme.SpecToEquivOfField _ _ u, (Scheme.SpecToEquivOfField _ _).left_inv u⟩
  have heq : (Scheme.SpecToEquivOfField _ (pullback f g)).symm ⟨t', ψ ≫ ρ⟩ =
      (Scheme.SpecToEquivOfField _ (pullback f g)).symm ⟨t₀, 𝟙 _⟩ := by
    show Spec.map (ψ ≫ ρ) ≫ (pullback f g).fromSpecResidueField t' = Spec.map (𝟙 _) ≫ (pullback f g).fromSpecResidueField t₀
    rw [Spec.map_comp, Category.assoc, hψ, hu, Spec.map_id, Category.id_comp]
  have hinj := (Scheme.SpecToEquivOfField _ (pullback f g)).symm.injective heq
  rw [Scheme.SpecToEquivOfField_eq_iff] at hinj
  obtain ⟨e', he'⟩ := hinj
  dsimp only at he'

  have hfun : ∀ w, ρ.hom (ψ.hom w) = ((pullback f g).residueFieldCongr e').hom.hom w := fun w => by
    have hw := congrArg (fun χ => χ.hom w) he'
    simp at hw
    exact hw
  intro z
  refine ⟨ψ.hom (((pullback f g).residueFieldCongr e').inv.hom z), ?_⟩
  show ρ.hom (ψ.hom _) = z
  rw [hfun, ← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]

end S_AlgebraicGeometry_IsPullback_surjective_residueFieldMap_of_isIso_residueFieldMap
end P2MW
export P2MW.S_AlgebraicGeometry_IsPullback_surjective_residueFieldMap_of_isIso_residueFieldMap (solution)
