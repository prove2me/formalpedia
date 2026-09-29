-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.IsFibreReading.eq_of_isFibreReading_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2be2b101-74f5-5544-89c3-80da23fa0f6d

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_of_isFibreReading_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
p2m_open "IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"
open scoped TensorProduct

universe u

namespace T3P3a

theorem app_res_top {X Y : Scheme.{u}} (i : X ⟶ Y) (U : Y.Opens) (x : Γ(Y, ⊤)) :
    (i.app U).hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom x) =
      (X.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ U ≤ ⊤)).op).hom ((i.appTop).hom x) := by
  have := i.naturality (homOfLE (le_top : U ≤ ⊤)).op
  have h := congrArg (fun k => k.hom x) this
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [h]
  congr 2

theorem specMap_appTop_ΓSpecIso_inv {B k : Type u} [CommRing B] [CommRing k] (r : B →+* k) (b : B) :
    (Spec.map (CommRingCat.ofHom r)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (r b) := by
  have := congrArg (fun f => f.hom b) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r))
  exact this.symm

end T3P3a

open T3P3a in
theorem solution
    {B₁ : Type u} [CommRing B₁] [IsLocalRing B₁]
    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [Flat f]
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X)
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (U : X.Opens) (hU : IsAffineOpen U) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (δ : Γ(X, U))
    (w w' : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).obj W)
    (hw : IsFibreReading V ι f fk i U W hW δ w) (hw' : IsFibreReading V ι f fk i U W hW δ w') :
    w = w' := by
  classical
  letI algU : Algebra B₁ Γ(X, U) := algebraOfHom f U
  letI algUk : Algebra (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U) := algebraOfHom fk (i ⁻¹ᵁ U)
  letI algW : Algebra (ResidueField B₁) Γ(Xk, W) := algebraOfHom fk W

  haveI : Module.Flat B₁ Γ(X, U) := by
    have hfl : ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appLE ⊤ U le_top).hom.Flat := by
      rw [CommRingCat.hom_comp]
      exact RingHom.Flat.comp
        (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B₁)).inv))
        (HasRingHomProperty.appLE @Flat f ‹Flat f› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top)
    exact hfl

  have hcompat : ∀ b : B₁, (i.app U).hom (algebraMap B₁ Γ(X, U) b) =
      algebraMap (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U) (residue B₁ b) := by
    intro b
    show (i.app U).hom ((f.app ⊤ ≫ X.presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom b)) =
      (fk.app ⊤ ≫ Xk.presheaf.map (homOfLE le_top).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField B₁))).inv.hom (residue B₁ b))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    refine (app_res_top i U _).trans ?_
    have h2 : (i.appTop).hom ((f.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom b)) =
        (fk.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField B₁))).inv.hom (residue B₁ b)) := by
      change (i.appTop).hom ((f.appTop).hom _) = (fk.appTop).hom _
      have := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom b)) (Scheme.Hom.comp_appTop i f)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [← this, hi.w, Scheme.Hom.comp_appTop]
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      rw [specMap_appTop_ΓSpecIso_inv]
    rw [h2]
    rfl

  let T : Type u := (OModulePresheaf.unit fk).obj W
  letI modT : Module B₁ T := Module.compHom T (residue B₁)
  have smul_def : ∀ (b : B₁) (t : T), b • t = (residue B₁ b) • t := fun _ _ => rfl
  let ρ : Γ(X, U) → T := fun s =>
    (OModulePresheaf.unit fk).res hW (show (OModulePresheaf.unit fk).obj (i ⁻¹ᵁ U) from (i.app U).hom s)
  have ρ_add : ∀ s s', ρ (s + s') = ρ s + ρ s' := fun s s' => by
    simp only [ρ, map_add]; exact map_add _ _ _
  have ρ_smul : ∀ (b : B₁) (s : Γ(X, U)), ρ (b • s) = b • ρ s := fun b s => by
    simp only [ρ, Algebra.smul_def, map_mul, hcompat, smul_def]
    show (Xk.presheaf.map (homOfLE hW).op).hom (algebraMap _ _ (residue B₁ b) * (i.app U).hom s) =
      residue B₁ b • (Xk.presheaf.map (homOfLE hW).op).hom ((i.app U).hom s)
    rw [map_mul, Algebra.smul_def]
    congr 1
    exact ((restrictAlgHom fk hW).commutes (residue B₁ b))
  have Bξ : ∀ ξ : Module.Dual (ResidueField B₁) V, ∃ B : V ⊗[B₁] Γ(X, U) →ₗ[B₁] T,
      ∀ v s, B (v ⊗ₜ s) = ξ v • ρ s := by
    intro ξ
    refine ⟨TensorProduct.lift (LinearMap.mk₂ B₁ (fun v s => ξ v • ρ s) ?_ ?_ ?_ ?_), fun v s => TensorProduct.lift.tmul _ _⟩
    · intro v v' s; rw [map_add, add_smul]
    · intro b v s
      rw [show b • v = (residue B₁ b) • v from (IsScalarTower.algebraMap_smul (ResidueField B₁) b v).symm,
        map_smul, smul_eq_mul, mul_smul, smul_def]
    · intro v s s'; rw [ρ_add, smul_add]
    · intro b v s; rw [ρ_smul, smul_def, smul_def, smul_smul, smul_smul, mul_comm]

  let μ : V ⊗[B₁] Γ(X, U) →ₗ[B₁] Γ(X, U) := (TensorProduct.lid B₁ Γ(X, U)).toLinearMap ∘ₗ LinearMap.rTensor Γ(X, U) ι
  have hμ : Function.Injective μ :=
    (TensorProduct.lid B₁ Γ(X, U)).injective.comp (Module.Flat.rTensor_preserves_injective_linearMap ι hι)
  have hμ_tmul : ∀ v s, μ (v ⊗ₜ s) = algebraMap B₁ Γ(X, U) (ι v) * s := fun v s => by
    simp only [μ, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
      Algebra.smul_def]

  obtain ⟨n, v, s, hδ, hwξ⟩ := hw
  obtain ⟨n', v', s', hδ', hwξ'⟩ := hw'
  have hsum : (∑ j, v j ⊗ₜ[B₁] s j) = ∑ j, v' j ⊗ₜ[B₁] s' j := by
    apply hμ
    rw [map_sum, map_sum]
    simp only [hμ_tmul]
    rw [hδ, hδ']
  ext ξ
  obtain ⟨B, hB⟩ := Bξ ξ
  rw [hwξ ξ, hwξ' ξ]
  have e1 : (∑ j, ξ (v j) • ρ (s j)) = B (∑ j, v j ⊗ₜ[B₁] s j) := by rw [map_sum]; simp only [hB]
  have e2 : (∑ j, ξ (v' j) • ρ (s' j)) = B (∑ j, v' j ⊗ₜ[B₁] s' j) := by rw [map_sum]; simp only [hB]
  show (∑ j, ξ (v j) • ρ (s j)) = ∑ j, ξ (v' j) • ρ (s' j)
  rw [e1, e2, hsum]

end S_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_of_isFibreReading_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_of_isFibreReading_of_flat (solution)
