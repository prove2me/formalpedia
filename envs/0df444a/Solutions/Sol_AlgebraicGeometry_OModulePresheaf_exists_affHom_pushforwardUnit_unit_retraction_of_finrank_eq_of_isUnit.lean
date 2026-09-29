-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/627e3c3a-2407-5db0-9d46-3ed14ccd6dc2

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_Module_Finite_exists_trace_end_eq_sum_dual_apply_of_projective
import Theorems.Thm_Module_sum_dual_apply_eq_natCast_of_rankAtStalk_eq
import Theorems.Thm_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq
import Theorems.Thm_AlgebraicGeometry_IsAffineHom_isPushout_map_appLE_appLE_map_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace Ws23TS

variable {R : Type u} [CommRing R] {V W : Scheme.{u}}

abbrev secHom (γ : W ⟶ V) (U : V.Opens) : Γ(V, U) →+* Γ(W, γ ⁻¹ᵁ U) :=
  (γ.appLE U (γ ⁻¹ᵁ U) le_rfl).hom

@[reducible] def secAlg (γ : W ⟶ V) (U : V.Opens) : Algebra Γ(V, U) Γ(W, γ ⁻¹ᵁ U) :=
  (secHom γ U).toAlgebra

section PerOpen

variable (γ : W ⟶ V) [IsFinite γ] [Flat γ] [LocallyOfFinitePresentation γ]

theorem finite_sec (U : V.affineOpens) :
    letI := secAlg γ U.1
    Module.Finite Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1) := by
  have h := IsFinite.finite_app γ U.1 U.2
  rw [Scheme.Hom.app_eq_appLE] at h
  exact h

theorem flat_sec (U : V.affineOpens) :
    letI := secAlg γ U.1
    Module.Flat Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1) :=
  HasRingHomProperty.appLE @Flat γ inferInstance U ⟨γ ⁻¹ᵁ U.1, U.2.preimage γ⟩ le_rfl

theorem finitePresentation_sec (U : V.affineOpens) :
    letI := secAlg γ U.1
    Algebra.FinitePresentation Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1) :=
  HasRingHomProperty.appLE @LocallyOfFinitePresentation γ inferInstance U ⟨γ ⁻¹ᵁ U.1, U.2.preimage γ⟩ le_rfl

theorem projective_sec (U : V.affineOpens) :
    letI := secAlg γ U.1
    Module.Projective Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1) := by
  letI := secAlg γ U.1
  haveI := finite_sec γ U
  haveI := flat_sec γ U
  haveI := finitePresentation_sec γ U
  haveI := Module.FinitePresentation.of_finite_of_finitePresentation Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1)
  exact Module.freeLocus_eq_univ_iff.mp Module.freeLocus_eq_univ

theorem finrank_secHom (d : ℕ) (hd : ∀ x : V, γ.finrank x = d) (U : V.affineOpens) :
    ∀ q, (secHom γ U.1).finrank q = d := by
  haveI : IsAffine U.1 := U.2
  haveI : IsAffine (γ ⁻¹ᵁ U.1 : W.Opens) := U.2.preimage γ
  have h1 : ∀ y, (γ ∣_ U.1).finrank y = d := fun y => by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict γ U.1).flip]
    exact hd _
  have hfin : (γ ∣_ U.1).appTop.hom.Finite := (γ ∣_ U.1).finite_appTop
  have hflat : (γ ∣_ U.1).appTop.hom.Flat := (γ ∣_ U.1).flat_appTop
  haveI : IsFinite (Spec.map (γ ∣_ U.1).appTop) := (IsFinite.SpecMap_iff _).mpr hfin
  haveI : Flat (Spec.map (γ ∣_ U.1).appTop) := Flat.SpecMap_iff.mpr hflat
  have sq : IsPullback (γ ⁻¹ᵁ U.1).toScheme.isoSpec.hom (γ ∣_ U.1) (Spec.map (γ ∣_ U.1).appTop)
      (U.1 : V.Opens).toScheme.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality (γ ∣_ U.1)⟩
  have h2 : ∀ p, (γ ∣_ U.1).appTop.hom.finrank p = d := fun p => by
    obtain ⟨y, rfl⟩ := (U.1 : V.Opens).toScheme.isoSpec.hom.surjective p
    rw [← Scheme.Hom.finrank_SpecMap_eq_finrank hfin hflat, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ sq]
    exact h1 y

  have happ : (γ ∣_ U.1).appTop = (U.1 : V.Opens).topIso.hom ≫ γ.appLE U.1 (γ ⁻¹ᵁ U.1) le_rfl ≫ (γ ⁻¹ᵁ U.1).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]; exact Scheme.Hom.resLE_app_top γ le_rfl
  intro q
  have hfinLE : (γ.appLE U.1 (γ ⁻¹ᵁ U.1) le_rfl).hom.Finite := by
    have h := IsFinite.finite_app γ U.1 U.2
    rwa [Scheme.Hom.app_eq_appLE] at h
  have hflatLE : (γ.appLE U.1 (γ ⁻¹ᵁ U.1) le_rfl).hom.Flat :=
    HasRingHomProperty.appLE @Flat γ inferInstance U ⟨γ ⁻¹ᵁ U.1, U.2.preimage γ⟩ le_rfl
  have he₁ : Function.Bijective (U.1 : V.Opens).topIso.hom.hom :=
    ConcreteCategory.bijective_of_isIso (U.1 : V.Opens).topIso.hom
  have he₂ : Function.Bijective (γ ⁻¹ᵁ U.1).topIso.inv.hom :=
    ConcreteCategory.bijective_of_isIso (γ ⁻¹ᵁ U.1).topIso.inv
  have h1' : ((γ.appLE U.1 (γ ⁻¹ᵁ U.1) le_rfl).hom.comp (U.1 : V.Opens).topIso.hom.hom).Finite :=
    hfinLE.comp (RingHom.Finite.of_surjective _ he₁.2)
  have h2' : ((γ.appLE U.1 (γ ⁻¹ᵁ U.1) le_rfl).hom.comp (U.1 : V.Opens).topIso.hom.hom).Flat :=
    (RingHom.Flat.of_bijective he₁).comp hflatLE
  have heq : (γ ∣_ U.1).appTop.hom =
      (γ ⁻¹ᵁ U.1).topIso.inv.hom.comp ((γ.appLE U.1 (γ ⁻¹ᵁ U.1) le_rfl).hom.comp (U.1 : V.Opens).topIso.hom.hom) := by
    rw [happ]; rfl
  rw [← RingHom.finrank_comp_right_of_bijective (U.1 : V.Opens).topIso.hom.hom _ he₁ hfinLE hflatLE
      (PrimeSpectrum.comap (U.1 : V.Opens).topIso.hom.hom q) q rfl,
    ← RingHom.finrank_comp_left_of_bijective _ (γ ⁻¹ᵁ U.1).topIso.inv.hom he₂ h1' h2', ← heq]
  exact h2 _

theorem rankAtStalk_sec (d : ℕ) (hd : ∀ x : V, γ.finrank x = d) (U : V.affineOpens) :
    letI := secAlg γ U.1
    ∀ q : PrimeSpectrum Γ(V, U.1), Module.rankAtStalk (R := Γ(V, U.1)) Γ(W, γ ⁻¹ᵁ U.1) q = d := by
  intro q
  have := finrank_secHom γ d hd U q
  rwa [RingHom.finrank] at this

theorem exists_dualFamily (U : V.affineOpens) :
    letI := secAlg γ U.1
    ∃ (n : ℕ) (x : Fin n → Γ(W, γ ⁻¹ᵁ U.1))
      (φ : Fin n → (Γ(W, γ ⁻¹ᵁ U.1) →ₗ[Γ(V, U.1)] Γ(V, U.1))),
      ∀ m : Γ(W, γ ⁻¹ᵁ U.1), ∑ i, φ i m • x i = m := by
  letI := secAlg γ U.1
  haveI := finite_sec γ U
  haveI := projective_sec γ U
  obtain ⟨n, f, g, -, -, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1)
  refine ⟨n, fun i => f (Pi.basisFun Γ(V, U.1) (Fin n) i), fun i => (LinearMap.proj i).comp g,
    fun m => ?_⟩
  have hm : f (g m) = m := by simpa using LinearMap.congr_fun hfg m
  have hsum := (Pi.basisFun Γ(V, U.1) (Fin n)).sum_repr (g m)
  simp only [Pi.basisFun_repr] at hsum
  conv_rhs => rw [← hm, ← hsum]
  simp only [map_sum, map_smul, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]

def tr (U : V.affineOpens) :
    letI := secAlg γ U.1
    Γ(W, γ ⁻¹ᵁ U.1) →ₗ[Γ(V, U.1)] Γ(V, U.1) :=
  letI := secAlg γ U.1
  haveI := finite_sec γ U
  haveI := projective_sec γ U
  (Module.Finite.exists_trace_end_eq_sum_dual_apply_of_projective
      (A := Γ(V, U.1)) (M := Γ(W, γ ⁻¹ᵁ U.1))).choose ∘ₗ
    LinearMap.mul Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1)

theorem tr_eq_sum (U : V.affineOpens) :
    letI := secAlg γ U.1
    ∀ (n : ℕ) (x : Fin n → Γ(W, γ ⁻¹ᵁ U.1))
      (φ : Fin n → (Γ(W, γ ⁻¹ᵁ U.1) →ₗ[Γ(V, U.1)] Γ(V, U.1))),
      (∀ m : Γ(W, γ ⁻¹ᵁ U.1), ∑ i, φ i m • x i = m) →
        ∀ b : Γ(W, γ ⁻¹ᵁ U.1), tr γ U b = ∑ i, φ i (b * x i) := by
  letI := secAlg γ U.1
  haveI := finite_sec γ U
  haveI := projective_sec γ U
  intro n x φ hxφ b
  have := (Module.Finite.exists_trace_end_eq_sum_dual_apply_of_projective
      (A := Γ(V, U.1)) (M := Γ(W, γ ⁻¹ᵁ U.1))).choose_spec n x φ hxφ (LinearMap.mul Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1) b)
  exact this

theorem tr_secHom_mul (U : V.affineOpens) (a : Γ(V, U.1)) (b : Γ(W, γ ⁻¹ᵁ U.1)) :
    tr γ U (secHom γ U.1 a * b) = a * tr γ U b := by
  letI := secAlg γ U.1
  have : secHom γ U.1 a * b = a • b := rfl
  rw [this, map_smul, smul_eq_mul]

theorem tr_one (d : ℕ) (hd : ∀ x : V, γ.finrank x = d) (U : V.affineOpens) :
    tr γ U 1 = (d : Γ(V, U.1)) := by
  letI := secAlg γ U.1
  obtain ⟨n, x, φ, hxφ⟩ := exists_dualFamily γ U
  rw [tr_eq_sum γ U n x φ hxφ 1]
  simp only [one_mul]
  exact Module.sum_dual_apply_eq_natCast_of_rankAtStalk_eq x φ hxφ d (rankAtStalk_sec γ d hd U)

theorem tr_res {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (b : Γ(W, γ ⁻¹ᵁ U'.1)) :
    tr γ U ((W.presheaf.map (homOfLE (γ.preimage_mono h)).op).hom b) =
      (V.presheaf.map (homOfLE h).op).hom (tr γ U' b) := by
  classical

  let ρ : Γ(V, U'.1) →+* Γ(V, U.1) := (V.presheaf.map (homOfLE h).op).hom
  let σ : Γ(W, γ ⁻¹ᵁ U'.1) →+* Γ(W, γ ⁻¹ᵁ U.1) := (W.presheaf.map (homOfLE (γ.preimage_mono h)).op).hom
  have hcomm : (secHom γ U.1).comp ρ = σ.comp (secHom γ U'.1) := by
    have := (AlgebraicGeometry.IsAffineHom.isPushout_map_appLE_appLE_map_of_isAffineOpen γ U.2 U'.2 h).w

    have := congrArg CommRingCat.Hom.hom this
    simpa only [CommRingCat.hom_comp] using this
  letI algA'A : Algebra Γ(V, U'.1) Γ(V, U.1) := ρ.toAlgebra
  letI algA'B' : Algebra Γ(V, U'.1) Γ(W, γ ⁻¹ᵁ U'.1) := secAlg γ U'.1
  letI algAB : Algebra Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1) := secAlg γ U.1
  letI algB'B : Algebra Γ(W, γ ⁻¹ᵁ U'.1) Γ(W, γ ⁻¹ᵁ U.1) := σ.toAlgebra
  letI algA'B : Algebra Γ(V, U'.1) Γ(W, γ ⁻¹ᵁ U.1) := ((secHom γ U.1).comp ρ).toAlgebra
  haveI st1 : IsScalarTower Γ(V, U'.1) Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U.1) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI st2 : IsScalarTower Γ(V, U'.1) Γ(W, γ ⁻¹ᵁ U'.1) Γ(W, γ ⁻¹ᵁ U.1) :=
    IsScalarTower.of_algebraMap_eq' hcomm
  have hpo : Algebra.IsPushout Γ(V, U'.1) Γ(V, U.1) Γ(W, γ ⁻¹ᵁ U'.1) Γ(W, γ ⁻¹ᵁ U.1) :=
    CommRingCat.isPushout_iff_isPushout.mp
      (AlgebraicGeometry.IsAffineHom.isPushout_map_appLE_appLE_map_of_isAffineOpen γ U.2 U'.2 h)
  have hbc := hpo.out
  set f₀ := (IsScalarTower.toAlgHom Γ(V, U'.1) Γ(W, γ ⁻¹ᵁ U'.1) Γ(W, γ ⁻¹ᵁ U.1)).toLinearMap with hf₀
  have hf₀σ : ∀ m, f₀ m = σ m := fun m => rfl
  obtain ⟨n, x, φ, hxφ⟩ := exists_dualFamily γ U'
  obtain ⟨φ', hφ'1, hφ'2⟩ :=
    IsBaseChange.exists_dual_comp_eq_algebraMap_and_sum_smul_eq f₀ hbc x φ hxφ
  rw [tr_eq_sum γ U' n x φ hxφ b, tr_eq_sum γ U n (fun i => f₀ (x i)) φ' hφ'2 (σ b), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf₀σ, ← map_mul, ← hf₀σ, hφ'1]
  rfl

end PerOpen

section Retraction

p2m_open "AlgebraicGeometry.OModulePresheaf"

variable (π : V ⟶ Spec (.of R))

include π

theorem isUnit_natCast {d : ℕ} (hdu : IsUnit ((d : ℕ) : R)) (U : V.Opens) : IsUnit ((d : ℕ) : Γ(V, U)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  simpa only [map_natCast] using hdu.map (algebraMap R Γ(V, U))

def dinv {d : ℕ} (hdu : IsUnit ((d : ℕ) : R)) (U : V.Opens) : Γ(V, U) :=
  ((isUnit_natCast π hdu U).unit⁻¹ : Γ(V, U)ˣ)

theorem natCast_mul_dinv {d : ℕ} (hdu : IsUnit ((d : ℕ) : R)) (U : V.Opens) :
    (d : Γ(V, U)) * dinv π hdu U = 1 := by
  show ((isUnit_natCast π hdu U).unit : Γ(V, U)) * _ = 1
  rw [dinv, Units.mul_inv]

theorem dinv_mul_natCast {d : ℕ} (hdu : IsUnit ((d : ℕ) : R)) (U : V.Opens) :
    dinv π hdu U * (d : Γ(V, U)) = 1 := by
  rw [mul_comm, natCast_mul_dinv]

theorem map_dinv {d : ℕ} (hdu : IsUnit ((d : ℕ) : R)) {U U' : V.Opens} (h : U ≤ U') :
    (V.presheaf.map (homOfLE h).op).hom (dinv π hdu U') = dinv π hdu U := by
  have h1 : (V.presheaf.map (homOfLE h).op).hom (dinv π hdu U') * (d : Γ(V, U)) = 1 := by
    rw [← map_natCast (V.presheaf.map (homOfLE h).op).hom d, ← map_mul, dinv_mul_natCast, map_one]
  calc (V.presheaf.map (homOfLE h).op).hom (dinv π hdu U')
      = (V.presheaf.map (homOfLE h).op).hom (dinv π hdu U') * ((d : Γ(V, U)) * dinv π hdu U) := by
        rw [natCast_mul_dinv, mul_one]
    _ = dinv π hdu U := by rw [← mul_assoc, h1, one_mul]

def rfun (γ : W ⟶ V) [IsFinite γ] [Flat γ] [LocallyOfFinitePresentation γ]
    {d : ℕ} (hdu : IsUnit ((d : ℕ) : R)) (U : V.affineOpens) (b : Γ(W, γ ⁻¹ᵁ U.1)) : Γ(V, U.1) :=
  dinv π hdu U.1 * tr γ U b

section RFun

variable (γ : W ⟶ V) [IsFinite γ] [Flat γ] [LocallyOfFinitePresentation γ]
  {d : ℕ} (hdu : IsUnit ((d : ℕ) : R))

include hdu

theorem rfun_add (U : V.affineOpens) (b b' : Γ(W, γ ⁻¹ᵁ U.1)) :
    rfun π γ hdu U (b + b') = rfun π γ hdu U b + rfun π γ hdu U b' := by
  simp only [rfun, map_add, mul_add]

theorem rfun_secHom_mul (U : V.affineOpens) (a : Γ(V, U.1)) (b : Γ(W, γ ⁻¹ᵁ U.1)) :
    rfun π γ hdu U (secHom γ U.1 a * b) = a * rfun π γ hdu U b := by
  simp only [rfun, tr_secHom_mul, mul_left_comm]

theorem rfun_algebraMap_mul (U : V.affineOpens) (r : R) (b : Γ(W, γ ⁻¹ᵁ U.1)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U.1
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (γ ≫ π) (γ ⁻¹ᵁ U.1)
    rfun π γ hdu U (algebraMap R Γ(W, γ ⁻¹ᵁ U.1) r * b) = algebraMap R Γ(V, U.1) r * rfun π γ hdu U b := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U.1
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (γ ≫ π) (γ ⁻¹ᵁ U.1)
  rw [← OModulePresheaf.appLE_algebraMap (π := π) γ U.1 r]
  exact rfun_secHom_mul π γ hdu U _ b

theorem rfun_res {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (b : Γ(W, γ ⁻¹ᵁ U'.1)) :
    rfun π γ hdu U ((W.presheaf.map (homOfLE (γ.preimage_mono h)).op).hom b)
      = (V.presheaf.map (homOfLE h).op).hom (rfun π γ hdu U' b) := by
  simp only [rfun, map_mul, map_dinv, tr_res γ h]

theorem rfun_secHom (hd : ∀ x : V, γ.finrank x = d) (U : V.affineOpens) (a : Γ(V, U.1)) :
    rfun π γ hdu U (secHom γ U.1 a) = a := by
  rw [← mul_one (secHom γ U.1 a), rfun_secHom_mul, rfun, tr_one γ d hd U, dinv_mul_natCast, mul_one]

end RFun

def retraction (γ : W ⟶ V) [IsFinite γ] [Flat γ] [LocallyOfFinitePresentation γ]
    {d : ℕ} (hdu : IsUnit ((d : ℕ) : R)) : AffHom (pushforwardUnit π γ) (unit π) where
  app U :=
    { toFun := fun b => (show (unit π).obj U.1 from rfun π γ hdu U (show Γ(W, γ ⁻¹ᵁ U.1) from b))
      map_add' := fun b b' => rfun_add π γ hdu U b b'
      map_smul' := fun r b => rfun_algebraMap_mul π γ hdu U r b }
  app_smul U a b := rfun_secHom_mul π γ hdu U a b
  naturality {U U'} h := LinearMap.ext fun b => rfun_res π γ hdu h b

theorem retraction_app (γ : W ⟶ V) [IsFinite γ] [Flat γ] [LocallyOfFinitePresentation γ]
    {d : ℕ} (hdu : IsUnit ((d : ℕ) : R)) (U : V.affineOpens) (b : Γ(W, γ ⁻¹ᵁ U.1)) :
    (retraction π γ hdu).app U (show (pushforwardUnit π γ).obj U.1 from b)
      = (show (unit π).obj U.1 from rfun π γ hdu U b) := rfl

theorem retraction_secHom (γ : W ⟶ V) [IsFinite γ] [Flat γ] [LocallyOfFinitePresentation γ]
    {d : ℕ} (hd : ∀ x : V, γ.finrank x = d) (hdu : IsUnit ((d : ℕ) : R)) (U : V.affineOpens) (a : Γ(V, U.1)) :
    (retraction π γ hdu).app U (show (pushforwardUnit π γ).obj U.1 from secHom γ U.1 a)
      = (show (unit π).obj U.1 from a) :=
  rfun_secHom π γ hdu hd U a

end Retraction

end Ws23TS

open AlgebraicGeometry.OModulePresheaf in
theorem solution
    {R : Type u} [CommRing R] {V W : Scheme.{u}} (π : V ⟶ Spec (.of R))
    (γ : W ⟶ V) [IsFinite γ] [Flat γ] [LocallyOfFinitePresentation γ]
    (d : ℕ) (hd : ∀ x : V, γ.finrank x = d) (hdu : IsUnit ((d : ℕ) : R)) :
    ∃ r : OModulePresheaf.AffHom (OModulePresheaf.pushforwardUnit π γ) (OModulePresheaf.unit π),
      ∀ (U : V.affineOpens) (a : Γ(V, U.1)),
        r.app U (show (OModulePresheaf.pushforwardUnit π γ).obj U.1 from
            (γ.appLE U.1 (γ ⁻¹ᵁ U.1) le_rfl).hom a) =
          (show (OModulePresheaf.unit π).obj U.1 from a) :=
  ⟨Ws23TS.retraction π γ hdu, fun U a => Ws23TS.retraction_secHom π γ hd hdu U a⟩

end
end S_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit (solution)
