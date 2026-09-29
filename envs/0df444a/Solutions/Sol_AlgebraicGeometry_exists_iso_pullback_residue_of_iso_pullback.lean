-- Prove2me | solution 1 for AlgebraicGeometry.exists_iso_pullback_residue_of_iso_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/09d00d43-d88d-59cb-bfb7-42572179f890

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_iso_pullback_residue_of_iso_pullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁]
    (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    {X X₁ : Scheme.{u}} (toBase : X ⟶ Spec (CommRingCat.of A)) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase) :
    ∃ ρ : pullback toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≅
        pullback f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))),
      ρ.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) =
        pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
          e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) := by

  have hκcomp : (IsLocalRing.ResidueField.map ι₁).comp (IsLocalRing.residue A₁) = (IsLocalRing.residue A).comp ι₁ :=
    IsLocalRing.ResidueField.map_comp_residue ι₁
  have hbij : Function.Bijective (IsLocalRing.ResidueField.map ι₁) := by
    refine ⟨(IsLocalRing.ResidueField.map ι₁).injective, ?_⟩
    have h : Function.Surjective ((IsLocalRing.ResidueField.map ι₁).comp (IsLocalRing.residue A₁)) := by rw [hκcomp]; exact hres₁
    rw [RingHom.coe_comp] at h
    exact Function.Surjective.of_comp h
  have hε1 : (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom.comp (IsLocalRing.ResidueField.map ι₁) = RingHom.id _ := by
    ext x; exact (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm_apply_apply x
  have hε2 : (IsLocalRing.ResidueField.map ι₁).comp (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom = RingHom.id _ := by
    ext x; exact (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).apply_symm_apply x

  have hκ1 : (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁))) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map (CommRingCat.ofHom ι₁)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκcomp]
  have hκ2 : (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁))) ≫ (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hε2, CommRingCat.ofHom_id, Spec.map_id]
  have hκ3 : (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hε1, CommRingCat.ofHom_id, Spec.map_id]
  have hκ4 : (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map (CommRingCat.ofHom ι₁)) = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← hκcomp,
      ← RingHom.comp_assoc, hε1, RingHom.id_comp]

  have wF : (pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ f₁ =
      (pullback.snd toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁)))) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) := by
    calc (pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ f₁
        = pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ e₁.hom ≫ (pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) ≫ f₁) := by
          simp only [Category.assoc]
      _ = pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ (Spec.map (CommRingCat.ofHom ι₁)) := by
          rw [pullback.condition]; simp only [Category.assoc]
      _ = (pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ toBase) ≫ (Spec.map (CommRingCat.ofHom ι₁)) := by rw [he₁, Category.assoc]
      _ = pullback.snd toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map (CommRingCat.ofHom ι₁))) := by rw [pullback.condition, Category.assoc]
      _ = (pullback.snd toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁)))) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) := by rw [← hκ1, Category.assoc]

  have wG0 : pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ f₁ = (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) ≫ (Spec.map (CommRingCat.ofHom ι₁)) := by
    rw [pullback.condition]
    simp only [Category.assoc]
    rw [hκ4]
  have wG : (pullback.lift (pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁)))) (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) wG0 ≫ e₁.inv) ≫ toBase =
      (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom))) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) := by
    rw [Category.assoc, ← he₁, e₁.inv_hom_id_assoc, pullback.lift_snd, Category.assoc]

  refine ⟨⟨pullback.lift (pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) (pullback.snd toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁)))) wF,
    pullback.lift (pullback.lift (pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁)))) (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) wG0 ≫ e₁.inv)
      (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom))) wG, ?_, ?_⟩, ?_⟩
  ·
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, pullback.lift_fst]
      have hFG0 : pullback.lift (pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) (pullback.snd toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁)))) wF ≫
          pullback.lift (pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁)))) (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) wG0 =
          pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ e₁.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc]
        · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc,
            ← Category.assoc (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁))), hκ2, Category.id_comp, Category.assoc, he₁, pullback.condition]
      rw [← Category.assoc, hFG0, Category.assoc, e₁.hom_inv_id, Category.comp_id]
    · rw [Category.id_comp, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, hκ2, Category.comp_id]
  ·
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, e₁.inv_hom_id_assoc, pullback.lift_fst]
    · rw [Category.id_comp, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, hκ3, Category.comp_id]
  ·
    exact pullback.lift_fst _ _ _

end S_AlgebraicGeometry_exists_iso_pullback_residue_of_iso_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_exists_iso_pullback_residue_of_iso_pullback (solution)
