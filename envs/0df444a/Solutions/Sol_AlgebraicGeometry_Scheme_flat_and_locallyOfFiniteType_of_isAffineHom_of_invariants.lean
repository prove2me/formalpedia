-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b5f19774-3f2c-5979-879b-9cfb4425b5f7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace P2M
namespace InvFlatFT

section RingCore

variable {B₀ R A : Type*} [CommRing B₀] [CommRing R] [CommRing A]

theorem moduleFinite_and_finiteType [IsNoetherianRing B₀] [Algebra B₀ R] [Algebra B₀ A] [Algebra R A]
    [IsScalarTower B₀ R A] [FaithfulSMul R A]
    (H : Type*) [Group H] [Finite H] [MulSemiringAction H A] [Algebra.IsInvariant R A H]
    [Algebra.FiniteType B₀ A] :
    Module.Finite R A ∧ Algebra.FiniteType B₀ R := by
  haveI hint : Algebra.IsIntegral R A := Algebra.IsInvariant.isIntegral R A H
  haveI hftRA : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType B₀ R A
  haveI hfin : Module.Finite R A := Algebra.IsIntegral.finite
  refine ⟨hfin, ?_⟩
  have hAC : (⊤ : Subalgebra B₀ A).FG := Algebra.FiniteType.out
  have hBC : (⊤ : Submodule R A).FG := Module.Finite.fg_top
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  exact ⟨fg_of_fg_of_fg B₀ R A hAC hBC hinj⟩

theorem flat_of_injective [IsDedekindDomain B₀] [Algebra B₀ R] [Algebra B₀ A] [Algebra R A]
    [IsScalarTower B₀ R A] (hp : Function.Injective (algebraMap R A)) [Module.Flat B₀ A] :
    Module.Flat B₀ R := by
  haveI : Module.IsTorsionFree B₀ A := inferInstance
  haveI : Module.IsTorsionFree B₀ R :=
    hp.moduleIsTorsionFree (algebraMap R A) (fun c x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply])
  infer_instance

variable {H : Type*} [Group H]

def autOf (σ : H → A →+* A) (hσ1 : ∀ a, σ 1 a = a)
    (hσmul : ∀ h₁ h₂ a, σ (h₁ * h₂) a = σ h₂ (σ h₁ a)) (h : H) : A ≃+* A :=
  { σ h⁻¹ with
    toFun := σ h⁻¹
    invFun := σ h
    left_inv := fun a ↦ by
      show σ h (σ h⁻¹ a) = a
      rw [← hσmul, inv_mul_cancel, hσ1]
    right_inv := fun a ↦ by
      show σ h⁻¹ (σ h a) = a
      rw [← hσmul, mul_inv_cancel, hσ1] }

@[scoped simp] theorem autOf_apply (σ : H → A →+* A) (hσ1 : ∀ a, σ 1 a = a)
    (hσmul : ∀ h₁ h₂ a, σ (h₁ * h₂) a = σ h₂ (σ h₁ a)) (h : H) (a : A) :
    autOf σ hσ1 hσmul h a = σ h⁻¹ a := rfl

def autHom (σ : H → A →+* A) (hσ1 : ∀ a, σ 1 a = a)
    (hσmul : ∀ h₁ h₂ a, σ (h₁ * h₂) a = σ h₂ (σ h₁ a)) : H →* (A ≃+* A) where
  toFun := autOf σ hσ1 hσmul
  map_one' := by
    ext a
    simp [hσ1]
  map_mul' h₁ h₂ := by
    ext a
    simp only [autOf_apply, mul_inv_rev, RingAut.mul_apply]
    rw [hσmul]

theorem ringCore [IsDedekindDomain B₀] (r : B₀ →+* R) (p : R →+* A) (hp : Function.Injective p)
    [Finite H] (σ : H → A →+* A) (hσ1 : ∀ a, σ 1 a = a)
    (hσmul : ∀ h₁ h₂ a, σ (h₁ * h₂) a = σ h₂ (σ h₁ a))
    (hinv : ∀ a : A, (∀ h, σ h a = a) → ∃ x : R, p x = a)
    (hflat : (p.comp r).Flat) (hft : (p.comp r).FiniteType) :
    r.Flat ∧ r.FiniteType := by
  letI : Algebra B₀ R := r.toAlgebra
  letI : Algebra R A := p.toAlgebra
  letI : Algebra B₀ A := (p.comp r).toAlgebra
  haveI : IsScalarTower B₀ R A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  letI : MulSemiringAction H A := MulSemiringAction.compHom A (autHom σ hσ1 hσmul)
  have hsmul : ∀ (h : H) (a : A), h • a = σ h⁻¹ a := fun _ _ ↦ rfl
  haveI : Algebra.IsInvariant R A H :=
    ⟨fun a ha ↦ hinv a (fun h ↦ by simpa [hsmul] using ha h⁻¹)⟩
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hp
  haveI : Algebra.FiniteType B₀ A := hft
  haveI : Module.Flat B₀ A := hflat
  obtain ⟨_, hftR⟩ := moduleFinite_and_finiteType (B₀ := B₀) (R := R) (A := A) H
  exact ⟨flat_of_injective (B₀ := B₀) (R := R) (A := A) hp, hftR⟩

end RingCore

section Sections

variable {M : Scheme.{0}}

theorem appLE_apply_of_eq_id {f : M ⟶ M} (hf : f = 𝟙 M) (W : M.Opens) (e : W ≤ f ⁻¹ᵁ W)
    (s : Γ(M, W)) : f.appLE W W e s = s := by
  subst hf
  have h1 : (homOfLE e).op = 𝟙 (Opposite.op W) := Subsingleton.elim _ _
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, h1]
  erw [M.presheaf.map_id]
  rfl

theorem appLE_apply_of_eq_comp {f g k : M ⟶ M} (hk : k = f ≫ g) (W : M.Opens)
    (ef : W ≤ f ⁻¹ᵁ W) (eg : W ≤ g ⁻¹ᵁ W) (ek : W ≤ k ⁻¹ᵁ W) (s : Γ(M, W)) :
    k.appLE W W ek s = f.appLE W W ef (g.appLE W W eg s) := by
  subst hk
  have h := Scheme.Hom.appLE_comp_appLE f g W W W eg ef
  have h' : (f ≫ g).appLE W W ek = g.appLE W W eg ≫ f.appLE W W ef := h.symm
  rw [h', CommRingCat.comp_apply]

end Sections

section SchemeShell

variable {B₀ : Type} [CommRing B₀] [IsDedekindDomain B₀]

theorem key {M X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of B₀))
    (π : M ⟶ X)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hflat : Flat (π ≫ πX)) (hlft : LocallyOfFiniteType (π ≫ πX)) (V : X.affineOpens) :
    RingHom.Flat (πX.appLE ⊤ V le_top).hom ∧ RingHom.FiniteType (πX.appLE ⊤ V le_top).hom := by
  haveI := haff

  let U : M.affineOpens := ⟨π ⁻¹ᵁ (V : X.Opens), V.2.preimage π⟩
  have hWle : ∀ h : H, (π ⁻¹ᵁ (V : X.Opens)) ≤ (ρ h).hom ⁻¹ᵁ (π ⁻¹ᵁ (V : X.Opens)) := fun h ↦ by
    rw [← Scheme.Hom.comp_preimage, hπ h]

  let T : (Spec (CommRingCat.of B₀)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hflatU : RingHom.Flat ((π ≫ πX).appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE (P := @Flat) (π ≫ πX) hflat T U le_top
  have hlftU : RingHom.FiniteType ((π ≫ πX).appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (π ≫ πX) hlft T U le_top
  have hcomp : (π ≫ πX).appLE ⊤ U le_top = πX.appLE ⊤ V le_top ≫ π.app V := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rw [hcomp] at hflatU hlftU

  let ι : CommRingCat.of B₀ ⟶ Γ(Spec (CommRingCat.of B₀), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B₀)).inv
  haveI : IsIso ι := inferInstance
  have hflat' : RingHom.Flat ((π.app V).hom.comp ((πX.appLE ⊤ V le_top).hom.comp ι.hom)) := by
    have := (RingHom.Flat.respectsIso.cancel_left_isIso ι (πX.appLE ⊤ V le_top ≫ π.app V)).mpr
      (by simpa [CommRingCat.hom_comp] using hflatU)
    simpa [CommRingCat.hom_comp, RingHom.comp_assoc] using this
  have hlft' : RingHom.FiniteType ((π.app V).hom.comp ((πX.appLE ⊤ V le_top).hom.comp ι.hom)) := by
    have := (RingHom.finiteType_respectsIso.cancel_left_isIso ι (πX.appLE ⊤ V le_top ≫ π.app V)).mpr
      (by simpa [CommRingCat.hom_comp] using hlftU)
    simpa [CommRingCat.hom_comp, RingHom.comp_assoc] using this

  let σ : H → Γ(M, π ⁻¹ᵁ (V : X.Opens)) →+* Γ(M, π ⁻¹ᵁ (V : X.Opens)) := fun h ↦
    ((ρ h).hom.appLE (π ⁻¹ᵁ (V : X.Opens)) (π ⁻¹ᵁ (V : X.Opens)) (hWle h)).hom
  have hσ1 : ∀ a, σ 1 a = a := fun a ↦ by
    have h1 : (ρ 1).hom = 𝟙 M := by rw [map_one]; rfl
    exact appLE_apply_of_eq_id h1 _ (hWle 1) a
  have hσmul : ∀ h₁ h₂ a, σ (h₁ * h₂) a = σ h₂ (σ h₁ a) := fun h₁ h₂ a ↦ by
    have hk : (ρ (h₁ * h₂)).hom = (ρ h₂).hom ≫ (ρ h₁).hom := by rw [map_mul]; rfl
    exact appLE_apply_of_eq_comp hk _ (hWle h₂) (hWle h₁) (hWle (h₁ * h₂)) a
  have hinvV : ∀ a : Γ(M, π ⁻¹ᵁ (V : X.Opens)), (∀ h, σ h a = a) → ∃ x, (π.app V).hom x = a := by
    intro a ha
    have : a ∈ Set.range (π.app V) := by
      rw [hinv V]
      exact ha
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩

  obtain ⟨hF, hT⟩ := ringCore ((πX.appLE ⊤ V le_top).hom.comp ι.hom) (π.app V).hom (hsec V) σ hσ1 hσmul
    hinvV hflat' hlft'
  refine ⟨?_, ?_⟩
  · exact (RingHom.Flat.respectsIso.cancel_left_isIso ι (πX.appLE ⊤ V le_top)).mp hF
  · exact (RingHom.finiteType_respectsIso.cancel_left_isIso ι (πX.appLE ⊤ V le_top)).mp hT

theorem main {M X : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of B₀)) (πX : X ⟶ Spec (CommRingCat.of B₀))
    (π : M ⟶ X) (hπX : π ≫ πX = πM)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hflat : Flat πM) (hlft : LocallyOfFiniteType πM) :
    Flat πX ∧ LocallyOfFiniteType πX := by
  subst hπX
  have hk := key πX π ρ hπ haff hsec hinv hflat hlft
  refine ⟨?_, ?_⟩
  · exact HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun V : X.affineOpens ↦ V)
      (iSup_affineOpens_eq_top X) (fun V ↦ (hk V).1)
  · exact HasRingHomProperty.of_iSup_eq_top (P := @LocallyOfFiniteType) (fun V : X.affineOpens ↦ V)
      (iSup_affineOpens_eq_top X) (fun V ↦ (hk V).2)

end SchemeShell

end P2M.InvFlatFT
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants.P2M P2MW.S_AlgebraicGeometry_Scheme_flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants.P2M.InvFlatFT"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants.P2M"

theorem solution
    {B₀ : Type} [CommRing B₀] [IsDedekindDomain B₀]
    {M X : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of B₀)) (πX : X ⟶ Spec (CommRingCat.of B₀))
    (π : M ⟶ X) (hπX : π ≫ πX = πM)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (hover : ∀ h : H, (ρ h).hom ≫ πM = πM)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hflat : Flat πM) (hlft : LocallyOfFiniteType πM) :
    Flat πX ∧ LocallyOfFiniteType πX :=
  P2M.InvFlatFT.main πM πX π hπX ρ hπ haff hsec hinv hflat hlft

end S_AlgebraicGeometry_Scheme_flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants (solution)
