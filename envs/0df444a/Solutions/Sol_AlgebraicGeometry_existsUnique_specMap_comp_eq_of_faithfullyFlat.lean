-- Prove2me | solution 1 for AlgebraicGeometry.existsUnique_specMap_comp_eq_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/911a7e73-ebe9-5a89-83d2-7f74a557862f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem solution
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B'] [Module.FaithfullyFlat B B']
    {T : Scheme.{u}} (φ' : Spec (CommRingCat.of B') ⟶ T)
    (h : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[B] B')) ≫ φ' =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B' →ₐ[B] B' ⊗[B] B').toRingHom) ≫ φ') :
    ∃! φ : Spec (CommRingCat.of B) ⟶ T, Spec.map (CommRingCat.ofHom (algebraMap B B')) ≫ φ = φ' := by
  have hff : (CommRingCat.ofHom (algebraMap B B')).hom.FaithfullyFlat := by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]; infer_instance
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap B B'))).mpr hff
  haveI := hflat
  haveI := hsurj
  haveI : EffectiveEpi (Spec.map (CommRingCat.ofHom (algebraMap B B'))) := inferInstance

  have hco : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ Spec (CommRingCat.of B')),
      g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B')) = g₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B')) →
      g₁ ≫ φ' = g₂ ≫ φ' := by
    intro Z g₁ g₂ hg
    have e1 : g₁ = pullback.lift g₁ g₂ hg ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have e2 : g₂ = pullback.lift g₁ g₂ hg ≫ pullback.snd _ _ := (pullback.lift_snd _ _ _).symm
    have key : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B B'))) (Spec.map (CommRingCat.ofHom (algebraMap B B'))) ≫ φ' =
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B B'))) (Spec.map (CommRingCat.ofHom (algebraMap B B'))) ≫ φ' := by
      rw [← pullbackSpecIso_hom_fst B B' B', ← pullbackSpecIso_hom_snd B B' B', Category.assoc, Category.assoc, h]
      rfl
    calc g₁ ≫ φ' = (pullback.lift g₁ g₂ hg ≫ pullback.fst _ _) ≫ φ' := by rw [← e1]
      _ = pullback.lift g₁ g₂ hg ≫ (pullback.snd _ _ ≫ φ') := by rw [Category.assoc, key]
      _ = g₂ ≫ φ' := by rw [← Category.assoc, ← e2]
  refine ⟨EffectiveEpi.desc _ φ' hco, EffectiveEpi.fac _ φ' hco, fun φ hφ => EffectiveEpi.uniq _ φ' hco φ hφ⟩

end S_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat
end P2MW
export P2MW.S_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat (solution)
