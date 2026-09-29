-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/759abc82-1c94-56b7-821d-8a0a7af660e8

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct TopologicalSpace Opposite

universe u

namespace P2mKDeg0

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
  (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)

theorem fromSpec_comp_eq :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  have h1 : CommRingCat.ofHom (algebraMap R Γ(X, U))
      = (Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top := rfl
  rw [h1, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top]

noncomputable def chart :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    Spec (.of (Γ(X, U) ⊗[R] Γ(Y, V))) ⟶ pullback f g :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  (pullbackSpecIso R Γ(X, U) Γ(Y, V)).inv ≫
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))))
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, V)))) f g hU.fromSpec hV.fromSpec (𝟙 _)
      (by rw [Category.comp_id, fromSpec_comp_eq]) (by rw [Category.comp_id, fromSpec_comp_eq])

scoped instance chart_isOpenImmersion : IsOpenImmersion (chart f g U hU V hV) := by
  unfold chart; infer_instance

theorem chart_fst :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    chart f g U hU V hV ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) ≫ hU.fromSpec := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  simp only [chart, Category.assoc, pullback.lift_fst]
  rw [pullbackSpecIso_inv_fst_assoc]

theorem chart_snd :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    chart f g U hU V hV ≫ pullback.snd f g =
      Spec.map (CommRingCat.ofHom (R := Γ(Y, V)) (S := Γ(X, U) ⊗[R] Γ(Y, V))
        (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight : Γ(Y, V) →ₐ[R] Γ(X, U) ⊗[R] Γ(Y, V)))) ≫
        hV.fromSpec := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  simp only [chart, Category.assoc, pullback.lift_snd]
  rw [pullbackSpecIso_inv_snd_assoc]

theorem opensRange_chart :
    (chart f g U hU V hV).opensRange = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  unfold chart
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  ext1
  simp only [Scheme.Hom.coe_opensRange, Opens.coe_inf, Scheme.Hom.coe_preimage]
  rw [Scheme.Pullback.range_map, IsAffineOpen.range_fromSpec, IsAffineOpen.range_fromSpec]

include hU hV in
theorem isAffineOpen_inf : IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  rw [← opensRange_chart f g U hU V hV]
  exact isAffineOpen_opensRange _

theorem top_le_preimage :
    (⊤ : (Spec (.of (letI := Scheme.TwoAffineOpenCover.algebraOfHom f U;
      letI := Scheme.TwoAffineOpenCover.algebraOfHom g V; Γ(X, U) ⊗[R] Γ(Y, V)))).Opens) ≤
      chart f g U hU V hV ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  rw [← opensRange_chart f g U hU V hV, Scheme.Hom.preimage_opensRange]

noncomputable def toTensor :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ⟶
      CommRingCat.of (Γ(X, U) ⊗[R] Γ(Y, V)) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  (chart f g U hU V hV).appLE _ ⊤ (top_le_preimage f g U hU V hV) ≫ (Scheme.ΓSpecIso _).hom

theorem appLE_congr_hom {P Q : Scheme.{u}} {φ ψ : P ⟶ Q} (h : φ = ψ) (U' : Q.Opens) (V' : P.Opens)
    (e : V' ≤ φ ⁻¹ᵁ U') : φ.appLE U' V' e = ψ.appLE U' V' (h ▸ e) := by
  subst h; rfl

scoped instance isIso_toTensor : IsIso (toTensor f g U hU V hV) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  have hW : chart f g U hU V hV ''ᵁ ⊤ = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    rw [Scheme.Hom.image_top_eq_opensRange, opensRange_chart]
  have key : (chart f g U hU V hV).appLE _ ⊤ (top_le_preimage f g U hU V hV)
      = (pullback f g).presheaf.map (eqToHom hW).op ≫ ((chart f g U hU V hV).appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  unfold toTensor
  rw [key]
  infer_instance

noncomputable def toTensorEquiv :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ≃+* Γ(X, U) ⊗[R] Γ(Y, V) :=
  (asIso (toTensor f g U hU V hV)).commRingCatIsoToRingEquiv

theorem toTensorEquiv_apply (x) : toTensorEquiv f g U hU V hV x = (toTensor f g U hU V hV).hom x := rfl

theorem top_le_fromSpec_preimage {P : Scheme.{u}} {U' : P.Opens} (hU' : IsAffineOpen U') :
    (⊤ : (Spec Γ(P, U')).Opens) ≤ hU'.fromSpec ⁻¹ᵁ U' := by
  intro x _
  show hU'.fromSpec.base x ∈ (U' : Set P)
  rw [← hU'.range_fromSpec]
  exact ⟨x, rfl⟩

theorem appLE_top_top {P Q : Scheme.{u}} (φ : P ⟶ Q) (e : (⊤ : P.Opens) ≤ φ ⁻¹ᵁ ⊤) :
    φ.appLE ⊤ ⊤ e = φ.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem fromSpec_appLE_top {P : Scheme.{u}} {U' : P.Opens} (hU' : IsAffineOpen U')
    (e : (⊤ : (Spec Γ(P, U')).Opens) ≤ hU'.fromSpec ⁻¹ᵁ U') :
    hU'.fromSpec.appLE U' ⊤ e = (Scheme.ΓSpecIso Γ(P, U')).inv := by
  rw [Scheme.Hom.appLE, hU'.fromSpec_app_of_le U' le_rfl]
  simp only [Category.assoc, ← Functor.map_comp]
  have h1 : (homOfLE (le_refl U')).op = 𝟙 (op U') := Subsingleton.elim _ _
  have h2 : ((homOfLE (le_top : hU'.fromSpec ⁻¹ᵁ U' ≤ ⊤)).op ≫ (homOfLE e).op :
      op (⊤ : (Spec Γ(P, U')).Opens) ⟶ op ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, h2, P.presheaf.map_id, (Spec Γ(P, U')).presheaf.map_id, Category.id_comp, Category.comp_id]

theorem toTensor_fst (a : Γ(X, U)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    (toTensor f g U hU V hV).hom ((pullback.fst f g).appLE U _ inf_le_left a) = a ⊗ₜ[R] (1 : Γ(Y, V)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  unfold toTensor
  rw [← CommRingCat.comp_apply, ← Category.assoc, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom (chart_fst f g U hU V hV), ← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤
      (top_le_fromSpec_preimage hU) le_top,
    fromSpec_appLE_top, appLE_top_top, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

theorem toTensor_snd (b : Γ(Y, V)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    (toTensor f g U hU V hV).hom ((pullback.snd f g).appLE V _ inf_le_right b) = (1 : Γ(X, U)) ⊗ₜ[R] b := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  unfold toTensor
  rw [← CommRingCat.comp_apply, ← Category.assoc, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom (chart_snd f g U hU V hV), ← Scheme.Hom.appLE_comp_appLE _ _ V ⊤ ⊤
      (top_le_fromSpec_preimage hV) le_top,
    fromSpec_appLE_top, appLE_top_top, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

theorem toTensorEquiv_symm_tmul_one (a : Γ(X, U)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    (toTensorEquiv f g U hU V hV).symm (a ⊗ₜ[R] (1 : Γ(Y, V))) =
      (pullback.fst f g).appLE U _ inf_le_left a := by
  rw [RingEquiv.symm_apply_eq, toTensorEquiv_apply, toTensor_fst]

theorem toTensorEquiv_symm_one_tmul (b : Γ(Y, V)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    (toTensorEquiv f g U hU V hV).symm ((1 : Γ(X, U)) ⊗ₜ[R] b) =
      (pullback.snd f g).appLE V _ inf_le_right b := by
  rw [RingEquiv.symm_apply_eq, toTensorEquiv_apply, toTensor_snd]

theorem appLE_algebraMap (r : R) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f g ≫ f)
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
    (pullback.fst f g).appLE U _ inf_le_left (algebraMap R Γ(X, U) r) =
      algebraMap R Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) r := by
  show ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top ≫ (pullback.fst f g).appLE U _ inf_le_left) r
    = ((Scheme.ΓSpecIso (.of R)).inv ≫ (pullback.fst f g ≫ f).appLE ⊤ _ le_top) r
  rw [Scheme.Hom.appLE_comp_appLE]

noncomputable def tensorAlgEquiv :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f g ≫ f)
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
    Γ(X, U) ⊗[R] Γ(Y, V) ≃ₐ[R] Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f g ≫ f)
    (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
  AlgEquiv.ofRingEquiv (f := (toTensorEquiv f g U hU V hV).symm) fun r => by
    rw [Algebra.TensorProduct.algebraMap_apply, toTensorEquiv_symm_tmul_one, appLE_algebraMap]

theorem tensorAlgEquiv_tmul (a : Γ(X, U)) (b : Γ(Y, V)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f g ≫ f)
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
    tensorAlgEquiv f g U hU V hV (a ⊗ₜ[R] b) =
      (pullback.fst f g).appLE U _ inf_le_left a * (pullback.snd f g).appLE V _ inf_le_right b := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  have h : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : Γ(Y, V))) * ((1 : Γ(X, U)) ⊗ₜ[R] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  show (toTensorEquiv f g U hU V hV).symm (a ⊗ₜ[R] b) = _
  rw [h, map_mul, toTensorEquiv_symm_tmul_one, toTensorEquiv_symm_one_tmul]

end P2mKDeg0
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage.P2mKDeg0"

open P2mKDeg0 in
theorem solution
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f g ≫ f)
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ∧
    ∃ e : Γ(X, U) ⊗[R] Γ(Y, V) ≃ₐ[R]
        Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V),
      ∀ (a : Γ(X, U)) (b : Γ(Y, V)), e (a ⊗ₜ[R] b) =
        (pullback.fst f g).appLE U (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_left a *
          (pullback.snd f g).appLE V (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_right b :=
  ⟨isAffineOpen_inf f g U hU V hV, tensorAlgEquiv f g U hU V hV, tensorAlgEquiv_tmul f g U hU V hV⟩

end S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage (solution)
