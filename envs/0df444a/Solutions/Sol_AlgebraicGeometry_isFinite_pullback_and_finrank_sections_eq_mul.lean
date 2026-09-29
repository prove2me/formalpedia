-- Prove2me | solution 1 for AlgebraicGeometry.isFinite_pullback_and_finrank_sections_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d3c27d5b-4e97-5946-b07f-275709343f08

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isFinite_pullback_and_finrank_sections_eq_mul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open TensorProduct

namespace KunnethFinrank

theorem finrank_eq_of_ringEquiv {κ : Type*} [CommSemiring κ] {T₁ T₂ : Type*} [Semiring T₁] [Semiring T₂]
    (i₁ : Algebra κ T₁) (i₂ : Algebra κ T₂) (h : T₁ ≃+* T₂)
    (hc : ∀ r, h (@algebraMap κ T₁ _ _ i₁ r) = @algebraMap κ T₂ _ _ i₂ r) :
    @Module.finrank κ T₁ _ _ i₁.toModule = @Module.finrank κ T₂ _ _ i₂.toModule := by
  letI := i₁; letI := i₂
  exact (AlgEquiv.ofRingEquiv (f := h) hc).toLinearEquiv.finrank_eq

theorem finrank_eq_of_algebraMap_eq {κ : Type*} [CommSemiring κ] {T : Type*} [Semiring T]
    (i₁ i₂ : Algebra κ T) (hc : ∀ r, @algebraMap κ T _ _ i₁ r = @algebraMap κ T _ _ i₂ r) :
    @Module.finrank κ T _ _ i₁.toModule = @Module.finrank κ T _ _ i₂.toModule :=
  finrank_eq_of_ringEquiv i₁ i₂ (RingEquiv.refl T) hc

theorem appLE_top_top {κ : Type u} [Field κ] {X : Scheme.{u}} (q : X ⟶ Spec (.of κ)) :
    q.appLE ⊤ ⊤ le_top = q.appTop := by
  rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]
  rfl

end KunnethFinrank

open KunnethFinrank in

theorem solution
    {κ : Type u} [Field κ] {Y Z : Scheme.{u}}
    (qY : Y ⟶ Spec (.of κ)) (qZ : Z ⟶ Spec (.of κ)) [IsFinite qY] [IsFinite qZ] :
    IsFinite (pullback.fst qY qZ ≫ qY) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst qY qZ ≫ qY) ⊤
     letI := Scheme.TwoAffineOpenCover.algebraOfHom qY ⊤
     letI := Scheme.TwoAffineOpenCover.algebraOfHom qZ ⊤
     Module.finrank κ Γ(pullback qY qZ, ⊤) = Module.finrank κ Γ(Y, ⊤) * Module.finrank κ Γ(Z, ⊤)) := by
  refine ⟨inferInstance, ?_⟩
  haveI : IsAffine Y := isAffine_of_isAffineHom qY
  haveI : IsAffine Z := isAffine_of_isAffineHom qZ

  let iY' : Algebra κ Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of κ)).inv ≫ qY.appTop).hom.toAlgebra
  let iZ' : Algebra κ Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of κ)).inv ≫ qZ.appTop).hom.toAlgebra
  have hY : @Module.finrank κ Γ(Y, ⊤) _ _ (Scheme.TwoAffineOpenCover.algebraOfHom qY ⊤).toModule =
      @Module.finrank κ Γ(Y, ⊤) _ _ iY'.toModule :=
    finrank_eq_of_algebraMap_eq _ _ fun r => by
      show ((Scheme.ΓSpecIso (.of κ)).inv ≫ qY.appLE ⊤ ⊤ le_top).hom r = ((Scheme.ΓSpecIso (.of κ)).inv ≫ qY.appTop).hom r
      rw [appLE_top_top]
  have hZ : @Module.finrank κ Γ(Z, ⊤) _ _ (Scheme.TwoAffineOpenCover.algebraOfHom qZ ⊤).toModule =
      @Module.finrank κ Γ(Z, ⊤) _ _ iZ'.toModule :=
    finrank_eq_of_algebraMap_eq _ _ fun r => by
      show ((Scheme.ΓSpecIso (.of κ)).inv ≫ qZ.appLE ⊤ ⊤ le_top).hom r = ((Scheme.ΓSpecIso (.of κ)).inv ≫ qZ.appTop).hom r
      rw [appLE_top_top]
  rw [hY, hZ]
  letI : Algebra κ Γ(Z, ⊤) := iZ'

  let g : Spec (.of ↑Γ(Z, ⊤)) ⟶ Spec (.of κ) := Spec.map (CommRingCat.ofHom (algebraMap κ ↑Γ(Z, ⊤)))
  have hg' : g = Spec.map ((Scheme.ΓSpecIso (.of κ)).inv ≫ qZ.appTop) := rfl
  have hg : Z.isoSpec.hom ≫ g = qZ := by
    rw [hg', Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

  let π : pullback qY qZ ⟶ pullback qY g :=
    pullback.map qY qZ qY g (𝟙 Y) Z.isoSpec.hom (𝟙 _) (by simp) (by rw [Category.comp_id, hg])
  have hπ : π ≫ pullback.fst qY g = pullback.fst qY qZ := by
    rw [pullback.lift_fst, Category.comp_id]
  haveI : IsIso π := inferInstance
  let hiso : Γ(pullback qY g, ⊤) ≃+* Γ(pullback qY qZ, ⊤) :=
    (Scheme.Γ.mapIso (asIso π).op).commRingCatIsoToRingEquiv
  have hiso_apply : ∀ x, hiso x = π.appTop.hom x := fun x => rfl

  let iP' : Algebra κ Γ(pullback qY g, ⊤) :=
    ((Scheme.ΓSpecIso (.of κ)).inv ≫ (pullback.fst qY g ≫ qY).appTop).hom.toAlgebra
  have hP : @Module.finrank κ Γ(pullback qY qZ, ⊤) _ _
        (Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst qY qZ ≫ qY) ⊤).toModule =
      @Module.finrank κ Γ(pullback qY g, ⊤) _ _ iP'.toModule := by
    symm
    refine finrank_eq_of_ringEquiv iP' _ hiso fun r => ?_
    show π.appTop.hom (((Scheme.ΓSpecIso (.of κ)).inv ≫ (pullback.fst qY g ≫ qY).appTop).hom r) =
      ((Scheme.ΓSpecIso (.of κ)).inv ≫ (pullback.fst qY qZ ≫ qY).appLE ⊤ ⊤ le_top).hom r
    rw [appLE_top_top, ← hπ, Category.assoc, Scheme.Hom.comp_appTop π (pullback.fst qY g ≫ qY)]
    rfl
  rw [hP]

  obtain ⟨e9, -⟩ := exists_algEquiv_globalSections_pullback_spec_tensorProduct qY (↑Γ(Z, ⊤))
  letI iS : Algebra ↑Γ(Z, ⊤) Γ(pullback qY g, ⊤) :=
    ((Scheme.ΓSpecIso (.of ↑Γ(Z, ⊤))).inv ≫ (pullback.snd qY g).appTop).hom.toAlgebra
  letI : Algebra κ Γ(pullback qY g, ⊤) := iP'
  letI : Algebra κ Γ(Y, ⊤) := iY'
  haveI : IsScalarTower κ ↑Γ(Z, ⊤) Γ(pullback qY g, ⊤) := IsScalarTower.of_algebraMap_eq fun r => by
    show ((Scheme.ΓSpecIso (.of κ)).inv ≫ (pullback.fst qY g ≫ qY).appTop).hom r =
      ((Scheme.ΓSpecIso (.of ↑Γ(Z, ⊤))).inv ≫ (pullback.snd qY g).appTop).hom
        (((Scheme.ΓSpecIso (.of κ)).inv ≫ qZ.appTop).hom r)
    rw [pullback.condition, Scheme.Hom.comp_appTop, hg', ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have h9 := (e9.toLinearEquiv.restrictScalars κ).finrank_eq
  rw [← h9, Module.finrank_tensorProduct, mul_comm]

end S_AlgebraicGeometry_isFinite_pullback_and_finrank_sections_eq_mul
end P2MW
export P2MW.S_AlgebraicGeometry_isFinite_pullback_and_finrank_sections_eq_mul (solution)
