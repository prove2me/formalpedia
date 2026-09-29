-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/bd60e45b-13f6-5c0d-8c74-c209381872f0

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite

noncomputable section

namespace P2mTJ2b

section LinAut

variable {B : Type u} [CommRing B]

theorem linearEquiv_apply_eq (f : B ≃ₗ[B] B) (x : B) : f x = x * f 1 := by
  conv_lhs => rw [← mul_one x, ← smul_eq_mul, map_smul, smul_eq_mul]

theorem isUnit_linearEquiv_one (f : B ≃ₗ[B] B) : IsUnit (f 1) := by
  refine ⟨⟨f 1, f.symm 1, ?_, ?_⟩, rfl⟩
  · have h := linearEquiv_apply_eq f (f.symm 1)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [mul_comm]; exact h.symm
  · have h := linearEquiv_apply_eq f (f.symm 1)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

end LinAut

section IsoSections

variable {X : Scheme.{u}}

def isoSections {L L' : X.Modules} (φ : L ≅ L') (U : X.Opens) : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(L', U) where
  toFun := φ.hom.app U
  invFun := φ.inv.app U
  map_add' x y := map_add _ x y
  map_smul' r x := Scheme.Modules.Hom.app_smul _ r x
  left_inv x := by
    change (φ.hom.app U ≫ φ.inv.app U) x = x
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
  right_inv x := by
    change (φ.inv.app U ≫ φ.hom.app U) x = x
    rw [← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl

theorem isoSections_apply {L L' : X.Modules} (φ : L ≅ L') (U : X.Opens) (x : Γ(L, U)) :
    isoSections φ U x = φ.hom.app U x := rfl

theorem app_map {M N : X.Modules} (φ : M ⟶ N) {W₁ W₂ : X.Opens} (i : W₁ ⟶ W₂) (x : Γ(M, W₂)) :
    φ.app W₁ (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app W₂ x) :=
  PresheafOfModules.naturality_apply φ.val i.op x

end IsoSections

section Main

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
variable {L L' : X.Modules}
variable (t t' : (𝒱.cover c).A01ˣ)
variable (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.cover c).A0)
  (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.cover c).A1)
  (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.cover c).A01)
  (he0 : ∀ x, e01 ((𝒱.sectionsOf c L).r0 x) = (𝒱.cover c).ρ0 (e0 x))
  (he1 : ∀ y, e01 ((𝒱.sectionsOf c L).r1 y) = (t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1 y))
  (e0' : (𝒱.sectionsOf c L').M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.cover c).A0)
  (e1' : (𝒱.sectionsOf c L').M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.cover c).A1)
  (e01' : (𝒱.sectionsOf c L').M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.cover c).A01)
  (he0' : ∀ x, e01' ((𝒱.sectionsOf c L').r0 x) = (𝒱.cover c).ρ0 (e0' x))
  (he1' : ∀ y, e01' ((𝒱.sectionsOf c L').r1 y) = (t' : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1' y))

include he0 he1 he0' he1'

theorem exists_units_of_iso (φ : L ≅ L') :
    ∃ (a0 : (𝒱.cover c).A0ˣ) (a1 : (𝒱.cover c).A1ˣ),
      (t' : (𝒱.cover c).A01) =
        (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0) * t * (𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1) := by

  let ψ0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.sectionsOf c L').M0 := isoSections φ 𝒱.U0
  let ψ1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.sectionsOf c L').M1 := isoSections φ 𝒱.U1
  let ψ01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.sectionsOf c L').M01 :=
    isoSections φ (𝒱.U0 ⊓ 𝒱.U1)
  have hψ0 : ∀ m, ψ01 ((𝒱.sectionsOf c L).r0 m) = (𝒱.sectionsOf c L').r0 (ψ0 m) := fun m => app_map φ.hom _ m
  have hψ1 : ∀ m, ψ01 ((𝒱.sectionsOf c L).r1 m) = (𝒱.sectionsOf c L').r1 (ψ1 m) := fun m => app_map φ.hom _ m

  let f0 : (𝒱.cover c).A0 ≃ₗ[(𝒱.cover c).A0] (𝒱.cover c).A0 := e0.symm ≪≫ₗ ψ0 ≪≫ₗ e0'
  let f1 : (𝒱.cover c).A1 ≃ₗ[(𝒱.cover c).A1] (𝒱.cover c).A1 := e1.symm ≪≫ₗ ψ1 ≪≫ₗ e1'
  let f01 : (𝒱.cover c).A01 ≃ₗ[(𝒱.cover c).A01] (𝒱.cover c).A01 := e01.symm ≪≫ₗ ψ01 ≪≫ₗ e01'

  have hf0 : ∀ x, f01 ((𝒱.cover c).ρ0 x) = (𝒱.cover c).ρ0 (f0 x) := by
    intro x
    change e01' (ψ01 (e01.symm ((𝒱.cover c).ρ0 x))) = (𝒱.cover c).ρ0 (e0' (ψ0 (e0.symm x)))
    have h1 : e01.symm ((𝒱.cover c).ρ0 x) = (𝒱.sectionsOf c L).r0 (e0.symm x) := by
      rw [LinearEquiv.symm_apply_eq, he0, LinearEquiv.apply_symm_apply]
    rw [h1, hψ0, he0']
  have hf1 : ∀ y, f01 ((t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 y) =
      (t' : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (f1 y) := by
    intro y
    change e01' (ψ01 (e01.symm ((t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 y))) =
      (t' : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1' (ψ1 (e1.symm y)))
    have h1 : e01.symm ((t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 y) = (𝒱.sectionsOf c L).r1 (e1.symm y) := by
      rw [LinearEquiv.symm_apply_eq, he1, LinearEquiv.apply_symm_apply]
    rw [h1, hψ1, he1']
  obtain ⟨a0, ha0⟩ := isUnit_linearEquiv_one f0
  obtain ⟨a1, ha1⟩ := isUnit_linearEquiv_one f1

  have h01 : f01 1 = (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0) := by
    have := hf0 1
    rwa [map_one, ← ha0] at this

  have h2 : (t : (𝒱.cover c).A01) * f01 1 = (t' : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (a1 : (𝒱.cover c).A1) := by
    have := hf1 1
    rwa [map_one, mul_one, linearEquiv_apply_eq f01, ← ha1] at this
  refine ⟨a0, a1, ?_⟩
  rw [h01] at h2
  have hu : (𝒱.cover c).ρ1 (a1 : (𝒱.cover c).A1) * (𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  calc (t' : (𝒱.cover c).A01)
      = (t' : (𝒱.cover c).A01) * ((𝒱.cover c).ρ1 (a1 : (𝒱.cover c).A1) *
          (𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1)) := by rw [hu, mul_one]
    _ = ((t : (𝒱.cover c).A01) * (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0)) *
          (𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1) := by rw [← mul_assoc, ← h2]
    _ = _ := by ring

theorem nonempty_iso_of_units (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (a0 : (𝒱.cover c).A0ˣ) (a1 : (𝒱.cover c).A1ˣ)
    (h : (t' : (𝒱.cover c).A01) =
      (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0) * t * (𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1)) :
    Nonempty (L ≅ L') := by
  let a01 : (𝒱.cover c).A01ˣ := Units.map (𝒱.cover c).ρ0.toMonoidHom a0
  let E0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.sectionsOf c L').M0 :=
    e0 ≪≫ₗ LinearEquiv.smulOfUnit a0 ≪≫ₗ e0'.symm
  let E1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.sectionsOf c L').M1 :=
    e1 ≪≫ₗ LinearEquiv.smulOfUnit a1 ≪≫ₗ e1'.symm
  let E01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.sectionsOf c L').M01 :=
    e01 ≪≫ₗ LinearEquiv.smulOfUnit a01 ≪≫ₗ e01'.symm
  refine AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible
    𝒱 c L L' hL hL' E0 E1 E01 (fun m => ?_) (fun m => ?_)
  · change e01'.symm (a01 • e01 ((𝒱.sectionsOf c L).r0 m)) = (𝒱.sectionsOf c L').r0 (e0'.symm (a0 • e0 m))
    rw [LinearEquiv.symm_apply_eq, he0', LinearEquiv.apply_symm_apply, he0, Units.smul_def, Units.smul_def,
      smul_eq_mul, smul_eq_mul, map_mul]
    rfl
  · change e01'.symm (a01 • e01 ((𝒱.sectionsOf c L).r1 m)) = (𝒱.sectionsOf c L').r1 (e1'.symm (a1 • e1 m))
    rw [LinearEquiv.symm_apply_eq, he1', LinearEquiv.apply_symm_apply, he1, Units.smul_def, Units.smul_def,
      smul_eq_mul, smul_eq_mul, map_mul, h]
    change (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0) * ((t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1 m)) = _
    have hu : (𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1) * (𝒱.cover c).ρ1 (a1 : (𝒱.cover c).A1) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0) * ((t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1 m))
        = (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0) * ((t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1 m)) *
            ((𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1) * (𝒱.cover c).ρ1 (a1 : (𝒱.cover c).A1)) := by
          rw [hu, mul_one]
      _ = _ := by ring

end Main

end P2mTJ2b

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (t t' : (𝒱.cover c).A01ˣ)
    (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.cover c).A0)
    (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.cover c).A1)
    (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.cover c).A01)
    (he0 : ∀ x, e01 ((𝒱.sectionsOf c L).r0 x) = (𝒱.cover c).ρ0 (e0 x))
    (he1 : ∀ y, e01 ((𝒱.sectionsOf c L).r1 y) = (t : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1 y))
    (e0' : (𝒱.sectionsOf c L').M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.cover c).A0)
    (e1' : (𝒱.sectionsOf c L').M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.cover c).A1)
    (e01' : (𝒱.sectionsOf c L').M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.cover c).A01)
    (he0' : ∀ x, e01' ((𝒱.sectionsOf c L').r0 x) = (𝒱.cover c).ρ0 (e0' x))
    (he1' : ∀ y, e01' ((𝒱.sectionsOf c L').r1 y) = (t' : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 (e1' y)) :
    Nonempty (L ≅ L') ↔
      ∃ (a0 : (𝒱.cover c).A0ˣ) (a1 : (𝒱.cover c).A1ˣ),
        (t' : (𝒱.cover c).A01) =
          (𝒱.cover c).ρ0 (a0 : (𝒱.cover c).A0) * t * (𝒱.cover c).ρ1 ((a1⁻¹ : (𝒱.cover c).A1ˣ) : (𝒱.cover c).A1) :=
  ⟨fun ⟨φ⟩ => P2mTJ2b.exists_units_of_iso 𝒱 c t t' e0 e1 e01 he0 he1 e0' e1' e01' he0' he1' φ,
    fun ⟨a0, a1, h⟩ => P2mTJ2b.nonempty_iso_of_units 𝒱 c t t' e0 e1 e01 he0 he1 e0' e1' e01' he0' he1'
      hL hL' a0 a1 h⟩

end
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_iff_exists_units_of_sectionsOf_equiv_lineBundle (solution)
