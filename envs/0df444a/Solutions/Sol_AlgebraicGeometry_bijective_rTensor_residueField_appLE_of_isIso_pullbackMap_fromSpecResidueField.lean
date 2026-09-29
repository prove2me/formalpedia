-- Prove2me | solution 1 for AlgebraicGeometry.bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4c08927c-0970-5325-9e72-750c124232db

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

theorem solution
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (W : Y.Opens) (hW : IsAffineOpen W) (hyW : y ∈ W)
    (U : X.Opens) (hU : IsAffineOpen U) (hUW : U ≤ q ⁻¹ᵁ W) (hhU : IsAffineOpen (h ⁻¹ᵁ U)) :
    letI : Algebra Γ(Y, W) Γ(X, U) := (q.appLE W U hUW).hom.toAlgebra
    letI : Algebra Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) := (q.appLE W U hUW ≫ h.appLE U (h ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    letI : Algebra Γ(Y, W) (Y.residueField y) := (Y.evaluation W y hyW).hom.toAlgebra
    Function.Bijective
      ((AlgHom.mk (h.appLE U (h ⁻¹ᵁ U) le_rfl).hom (fun _ => rfl) :
          Γ(X, U) →ₐ[Γ(Y, W)] Γ(Z, h ⁻¹ᵁ U)).toLinearMap.rTensor (Y.residueField y)) := by
  classical

  letI iRA : Algebra Γ(Y, W) Γ(X, U) := (q.appLE W U hUW).hom.toAlgebra
  letI iRB : Algebra Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) := (q.appLE W U hUW ≫ h.appLE U (h ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI iRκ : Algebra Γ(Y, W) (Y.residueField y) := (Y.evaluation W y hyW).hom.toAlgebra
  show Function.Bijective
      ((AlgHom.mk (h.appLE U (h ⁻¹ᵁ U) le_rfl).hom (fun _ => rfl) :
          Γ(X, U) →ₐ[Γ(Y, W)] Γ(Z, h ⁻¹ᵁ U)).toLinearMap.rTensor (Y.residueField y))
  set ψ : Γ(X, U) →ₐ[Γ(Y, W)] Γ(Z, h ⁻¹ᵁ U) := AlgHom.mk (h.appLE U (h ⁻¹ᵁ U) le_rfl).hom (fun _ => rfl) with hψ

  have ea : Spec.map (q.appLE W U hUW) ≫ hW.fromSpec = hU.fromSpec ≫ q := IsAffineOpen.SpecMap_appLE_fromSpec q hW hU hUW
  have eb : Spec.map (h.appLE U (h ⁻¹ᵁ U) le_rfl) ≫ hU.fromSpec = hhU.fromSpec ≫ h :=
    IsAffineOpen.SpecMap_appLE_fromSpec h hU hhU le_rfl
  have ec : Spec.map (Y.evaluation W y hyW) ≫ hW.fromSpec = Y.fromSpecResidueField y := by
    rw [← Scheme.germ_residue, Spec.map_comp, Category.assoc]
    change Spec.map (Y.residue y) ≫ hW.fromSpecStalk hyW = _
    rw [IsAffineOpen.fromSpecStalk_eq_fromSpecStalk]
    rfl
  have hRA : Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(X, U))) = Spec.map (q.appLE W U hUW) := rfl
  have hRκ : Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) (Y.residueField y))) = Spec.map (Y.evaluation W y hyW) := rfl
  have hRB : Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(Z, h ⁻¹ᵁ U))) =
      Spec.map (h.appLE U (h ⁻¹ᵁ U) le_rfl) ≫ Spec.map (q.appLE W U hUW) := by
    rw [← Spec.map_comp]; rfl
  have hAB : Spec.map (CommRingCat.ofHom (ψ : Γ(X, U) →+* Γ(Z, h ⁻¹ᵁ U))) = Spec.map (h.appLE U (h ⁻¹ᵁ U) le_rfl) := by
    rw [hψ]; rfl

  set Hy := pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]) with hHy
  set jA : pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(X, U))))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) (Y.residueField y)))) ⟶ pullback q (Y.fromSpecResidueField y) :=
    pullback.map _ _ _ _ hU.fromSpec (𝟙 _) hW.fromSpec (by rw [hRA, ea]) (by rw [hRκ, ec, Category.id_comp]) with hjA
  set jB : pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(Z, h ⁻¹ᵁ U))))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) (Y.residueField y)))) ⟶ pullback p (Y.fromSpecResidueField y) :=
    pullback.map _ _ _ _ hhU.fromSpec (𝟙 _) hW.fromSpec
      (by rw [hRB, Category.assoc, ea, ← Category.assoc, eb, Category.assoc, w]) (by rw [hRκ, ec, Category.id_comp]) with hjB
  set g : pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(Z, h ⁻¹ᵁ U))))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) (Y.residueField y)))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(X, U))))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) (Y.residueField y)))) :=
    pullback.map _ _ _ _ (Spec.map (CommRingCat.ofHom (ψ : Γ(X, U) →+* Γ(Z, h ⁻¹ᵁ U)))) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, hRB, hAB, hRA]) (by rw [Category.comp_id, Category.id_comp]) with hg
  have hsq : g ≫ jA = jB ≫ Hy := by
    apply pullback.hom_ext
    · simp only [hg, hjA, hjB, hHy, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [hAB, eb]
    · simp only [hg, hjA, hjB, hHy, Category.assoc, pullback.lift_snd, Category.comp_id]

  haveI : IsIso Hy := hy
  have hgopen : IsOpenImmersion g := by
    haveI : IsOpenImmersion (g ≫ jA) := by rw [hsq]; infer_instance
    exact IsOpenImmersion.of_comp g jA

  have hgsurj : Function.Surjective g := by
    intro x
    haveI : Surjective Hy := ((isIso_iff_isOpenImmersion_and_surjective Hy).1 hy).2
    obtain ⟨z, hz⟩ := Hy.surjective (jA x)

    have hxU : (pullback.fst q (Y.fromSpecResidueField y)) (jA x) ∈ (U : Set X) := by
      rw [← IsAffineOpen.range_fromSpec hU]
      have hr : jA x ∈ Set.range jA := ⟨x, rfl⟩
      rw [hjA, Scheme.Pullback.range_map] at hr
      exact hr.1
    have hzU : (pullback.fst p (Y.fromSpecResidueField y)) z ∈ (h ⁻¹ᵁ U : Set Z) := by
      show h ((pullback.fst p (Y.fromSpecResidueField y)) z) ∈ (U : Set X)
      have hc : (pullback.fst p (Y.fromSpecResidueField y) ≫ h) z = (Hy ≫ pullback.fst q (Y.fromSpecResidueField y)) z := by
        rw [hHy, pullback.lift_fst]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz] at hc
      rw [hc]; exact hxU
    have hzr : z ∈ Set.range jB := by
      rw [hjB, Scheme.Pullback.range_map, IsAffineOpen.range_fromSpec]
      refine ⟨hzU, ?_⟩
      simp
    obtain ⟨b, rfl⟩ := hzr
    refine ⟨b, jA.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, hz]
  have hgiso : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).2 ⟨hgopen, ⟨hgsurj⟩⟩

  set T : Γ(X, U) ⊗[Γ(Y, W)] Y.residueField y →ₐ[Γ(Y, W)] Γ(Z, h ⁻¹ᵁ U) ⊗[Γ(Y, W)] Y.residueField y :=
    Algebra.TensorProduct.map ψ (AlgHom.id Γ(Y, W) (Y.residueField y)) with hT
  have hconj : (pullbackSpecIso Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) (Y.residueField y)).hom ≫
      Spec.map (CommRingCat.ofHom T.toRingHom) ≫ (pullbackSpecIso Γ(Y, W) Γ(X, U) (Y.residueField y)).inv = g := by
    apply pullback.hom_ext
    · have eL : g ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (ψ : Γ(X, U) →+* Γ(Z, h ⁻¹ᵁ U))) := by
        simp only [hg, pullback.lift_fst]
      rw [eL, ← pullbackSpecIso_hom_fst Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) (Y.residueField y), Category.assoc, Category.assoc,
        Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 3
    · have eR : g ≫ pullback.snd _ _ = pullback.snd _ _ := by
        simp only [hg, pullback.lift_snd, Category.comp_id]
      rw [eR, ← pullbackSpecIso_hom_snd Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) (Y.residueField y), Category.assoc, Category.assoc,
        pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      ext k
      simp [hT, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hSpecT : IsIso (Spec.map (CommRingCat.ofHom T.toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom T.toRingHom) =
        (pullbackSpecIso Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) (Y.residueField y)).inv ≫ g ≫
          (pullbackSpecIso Γ(Y, W) Γ(X, U) (Y.residueField y)).hom := by
      rw [← hconj]; simp
    rw [this]; infer_instance

  have hTiso : IsIso (CommRingCat.ofHom T.toRingHom) := by
    haveI : IsIso (Scheme.Spec.map (CommRingCat.ofHom T.toRingHom).op) := hSpecT
    haveI := Spec.fullyFaithful.isIso_of_isIso_map (CommRingCat.ofHom T.toRingHom).op
    exact isIso_unop (CommRingCat.ofHom T.toRingHom).op
  have hTbij : Function.Bijective T.toRingHom := by
    simpa using ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom T.toRingHom)
  have hfun : ⇑(ψ.toLinearMap.rTensor (Y.residueField y)) = ⇑T := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a k => simp [hT, Algebra.TensorProduct.map_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [hfun]
  exact hTbij

#print axioms solution

end S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField (solution)
