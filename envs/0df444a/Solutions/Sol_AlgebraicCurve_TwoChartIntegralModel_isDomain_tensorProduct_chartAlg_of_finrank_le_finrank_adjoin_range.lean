-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isDomain_tensorProduct_chartAlg_of_finrank_le_finrank_adjoin_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e58f0bb8-a57c-5b7c-b368-5bdd66b05fb5

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_span_singleton_isPrime_and_mem_iff_mem_nonunits_of_valuationSubring
import Theorems.Thm_IntermediateField_isDomain_tensorProduct_of_finrank_le_finrank_adjoin_range
import Theorems.Thm_IntermediateField_finrank_adjoin_range_le_finrank_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isDomain_tensorProduct_chartAlg_of_finrank_le_finrank_adjoin_range
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Polynomial

universe u

namespace DeuringAsm

section
variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F]

def toV (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V) : R →+* ↥V :=
  (algebraMap R F).codRestrict V.toSubring hRV

theorem coe_toV (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V) (r : R) :
    ((toV V hRV r : ↥V) : F) = algebraMap R F r := rfl

theorem residue_toV_eq_zero (ϖ : R) (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V)
    (hϖV : algebraMap R F ϖ ∈ V.nonunits) : IsLocalRing.residue ↥V (toV V hRV ϖ) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  exact hϖV

theorem isMaximal_span [IsDomain R] [IsPrincipalIdealRing R] {ϖ : R} (hϖ : Prime ϖ) :
    (Ideal.span {ϖ} : Ideal R).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible hϖ.irreducible

noncomputable def resHom (ϖ : R) (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V)
    (hϖV : algebraMap R F ϖ ∈ V.nonunits) : R ⧸ (Ideal.span {ϖ} : Ideal R) →+* IsLocalRing.ResidueField ↥V :=
  Ideal.Quotient.lift _ ((IsLocalRing.residue ↥V).comp (toV V hRV)) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [RingHom.comp_apply, map_mul, map_mul, residue_toV_eq_zero ϖ V hRV hϖV, zero_mul])

theorem resHom_mk (ϖ : R) (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V)
    (hϖV : algebraMap R F ϖ ∈ V.nonunits) (r : R) :
    resHom ϖ V hRV hϖV (Ideal.Quotient.mk _ r) = IsLocalRing.residue ↥V (toV V hRV r) := rfl

end

section BaseChange
variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F]

noncomputable abbrev algRκ (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V) :
    Algebra R (IsLocalRing.ResidueField ↥V) :=
  ((IsLocalRing.residue ↥V).comp (toV V hRV)).toAlgebra

noncomputable def redHom (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V)
    (𝒪 : Subalgebra R F) (hOV : ∀ a : ↥𝒪, (a : F) ∈ V) :
    letI := algRκ V hRV
    ↥𝒪 →ₐ[R] IsLocalRing.ResidueField ↥V :=
  letI := algRκ V hRV
  { toFun := fun a => IsLocalRing.residue ↥V ⟨a, hOV a⟩
    map_one' := by
      have : (⟨((1 : ↥𝒪) : F), hOV 1⟩ : ↥V) = 1 := Subtype.ext (by simp)
      rw [this, map_one]
    map_mul' := fun a b => by
      have : (⟨((a * b : ↥𝒪) : F), hOV (a * b)⟩ : ↥V) = ⟨a, hOV a⟩ * ⟨b, hOV b⟩ := Subtype.ext (by simp)
      rw [this, map_mul]
    map_zero' := by
      have : (⟨((0 : ↥𝒪) : F), hOV 0⟩ : ↥V) = 0 := Subtype.ext (by simp)
      rw [this, map_zero]
    map_add' := fun a b => by
      have : (⟨((a + b : ↥𝒪) : F), hOV (a + b)⟩ : ↥V) = ⟨a, hOV a⟩ + ⟨b, hOV b⟩ := Subtype.ext (by simp)
      rw [this, map_add]
    commutes' := fun r => by
      have : (⟨((algebraMap R ↥𝒪 r : ↥𝒪) : F), hOV _⟩ : ↥V) = toV V hRV r :=
        Subtype.ext (by simp [coe_toV, Subalgebra.coe_algebraMap])
      rw [this]
      rfl }

theorem redHom_apply (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V)
    (𝒪 : Subalgebra R F) (hOV : ∀ a : ↥𝒪, (a : F) ∈ V) (a : ↥𝒪) :
    letI := algRκ V hRV
    redHom V hRV 𝒪 hOV a = IsLocalRing.residue ↥V ⟨a, hOV a⟩ := rfl

end BaseChange

end DeuringAsm

section Helpers
open Polynomial AlgebraicCurve
namespace DeuringAsmH

theorem transcendental_inv {R K : Type*} [CommRing R] [Field K] [Algebra R K] {x : K} (hx : Transcendental R x) :
    Transcendental R x⁻¹ := fun h =>
  hx (by simpa using (IsAlgebraic.inv_iff (R := R) (x := x)).1 h)

theorem adjoin_inv_eq {K L : Type*} [Field K] [Field L] [Algebra K L] (j : L) :
    IntermediateField.adjoin K ({j⁻¹} : Set L) = IntermediateField.adjoin K ({j} : Set L) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact (IntermediateField.adjoin K ({j} : Set L)).inv_mem (IntermediateField.mem_adjoin_simple_self K j)
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    have h := (IntermediateField.adjoin K ({j⁻¹} : Set L)).inv_mem (IntermediateField.mem_adjoin_simple_self K j⁻¹)
    rwa [inv_inv] at h

theorem not_C_dvd_reverse {R : Type*} [CommRing R] {ϖ : R} {P : R[X]} (hP : ¬ C ϖ ∣ P) : ¬ C ϖ ∣ P.reverse := by
  intro h
  apply hP
  rw [C_dvd_iff_dvd_coeff] at h ⊢
  intro i
  by_cases hi : i ≤ P.natDegree
  · have := h (revAt P.natDegree i)
    rwa [coeff_reverse, revAt_invol] at this
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    exact dvd_zero _

theorem gaussType_inv {R F : Type*} [CommRing R] [Field F] [Algebra R F]
    {ϖ : R} (hϖ : ¬ IsUnit ϖ) {j : F} (hj : j ≠ 0) (V : ValuationSubring F)
    (hjV : ∀ P : R[X], ¬ (C ϖ ∣ P) → aeval j P ∈ V ∧ (aeval j P)⁻¹ ∈ V) :
    ∀ P : R[X], ¬ (C ϖ ∣ P) → aeval j⁻¹ P ∈ V ∧ (aeval j⁻¹ P)⁻¹ ∈ V := by

  have hX : ¬ C ϖ ∣ (X : R[X]) := by
    intro hd
    rw [C_dvd_iff_dvd_coeff] at hd
    have := hd 1
    rw [coeff_X_one] at this
    exact hϖ (isUnit_of_dvd_one this)
  obtain ⟨hjm, hjim⟩ := hjV X hX
  rw [aeval_X] at hjm hjim
  intro P hP
  obtain ⟨hr, hri⟩ := hjV P.reverse (not_C_dvd_reverse hP)

  letI : Invertible (j⁻¹) := invertibleOfNonzero (inv_ne_zero hj)
  have hkey : aeval j⁻¹ P = aeval j P.reverse * (j⁻¹) ^ P.natDegree := by
    have h := eval₂_reverse_mul_pow (algebraMap R F) j⁻¹ P
    rw [invOf_eq_inv, inv_inv] at h
    rw [aeval_def, aeval_def, ← h]
  refine ⟨?_, ?_⟩
  · rw [hkey]
    exact mul_mem hr (pow_mem hjim _)
  · rw [hkey, mul_inv, ← inv_pow, inv_inv]
    exact mul_mem hri (pow_mem hjm _)

theorem chartAlg_le (R F : Type u) [CommRing R] [Field F] [Algebra R F] (S : Set F)
    (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V) (hS : ∀ s ∈ S, s ∈ V) :
    ∀ a : ↥(TwoChartIntegralModel.chartAlg R F S), (a : F) ∈ V := by
  have hAV : ∀ x ∈ Algebra.adjoin R S, x ∈ V := by
    intro x hx
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · intro y hy; exact hS y hy
    · intro r; exact hRV r
    · intro x y _ _ hx hy; exact add_mem hx hy
    · intro x y _ _ hx hy; exact mul_mem hx hy
  intro a
  obtain ⟨p, hpm, hpx⟩ := (TwoChartIntegralModel.mem_chartAlg_iff R F).1 a.2
  let ψ : ↥(Algebra.adjoin R S) →+* ↥V :=
    (Subalgebra.val (Algebra.adjoin R S)).toRingHom.codRestrict V.toSubring (fun x => hAV x x.2)
  have hint : IsIntegral ↥V (a : F) := by
    refine ⟨p.map ψ, hpm.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpx
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← hv]
  exact v.2

theorem chartAlgMid_le (R F : Type u) [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V) (hj : j ∈ V) (hji : j⁻¹ ∈ V) :
    ∀ a : ↥(TwoChartIntegralModel.chartAlgMid R F j), (a : F) ∈ V :=
  chartAlg_le R F {j, j⁻¹} V hRV (by
    intro s hs
    rcases hs with rfl | hs
    · exact hj
    · rw [Set.mem_singleton_iff] at hs; subst hs; exact hji)

theorem chartAlgFin_le (R F : Type u) [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V) (hj : j ∈ V) :
    ∀ a : ↥(TwoChartIntegralModel.chartAlgFin R F j), (a : F) ∈ V :=
  chartAlg_le R F {j} V hRV (by intro s hs; rw [Set.mem_singleton_iff] at hs; subst hs; exact hj)

theorem chartAlgInf_le (R F : Type u) [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (V : ValuationSubring F) (hRV : ∀ r : R, algebraMap R F r ∈ V) (hji : j⁻¹ ∈ V) :
    ∀ a : ↥(TwoChartIntegralModel.chartAlgInf R F j), (a : F) ∈ V :=
  chartAlg_le R F {j⁻¹} V hRV (by intro s hs; rw [Set.mem_singleton_iff] at hs; subst hs; exact hji)

end DeuringAsmH
end Helpers

open DeuringAsm AlgebraicCurve

open AlgebraicCurve.TwoChartIntegralModel in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (V : ValuationSubring F)
    (hRV : ∀ r : R, algebraMap R F r ∈ V) (hϖV : algebraMap R F ϖ ∈ V.nonunits)
    (hjV : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
    (k : Type u) [Field k] [Algebra R k] (hk : algebraMap R k ϖ = 0)
    (Ω : Type u) [Field Ω] [Algebra k Ω]
    (ρ : ↥V →+* Ω) (hρ : ∀ x : ↥V, (x : F) ∈ V.nonunits → ρ x = 0)
    (hρR : ∀ r : R, ρ ⟨algebraMap R F r, hRV r⟩ = algebraMap k Ω (algebraMap R k r))
    (jV : ↥V) (hjV' : (jV : F) = j)
    (t : ↥(IntermediateField.adjoin k (Set.range ρ))) (ht : (t : Ω) = ρ jV)
    (htr : Transcendental k t)
    (hdeg : Module.finrank ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F ≤
      Module.finrank ↥(IntermediateField.adjoin k ({t} : Set ↥(IntermediateField.adjoin k (Set.range ρ))))
        ↥(IntermediateField.adjoin k (Set.range ρ))) :
    IsDomain (k ⊗[R] ↥(chartAlgFin R F j)) ∧ IsDomain (k ⊗[R] ↥(chartAlgInf R F j)) ∧
      Nontrivial (k ⊗[R] ↥(chartAlgMid R F j)) := by
  classical
  haveI hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal := isMaximal_span hϖ
  letI : Field (R ⧸ (Ideal.span {ϖ} : Ideal R)) := Ideal.Quotient.field _

  letI algFκ : Algebra (R ⧸ (Ideal.span {ϖ} : Ideal R)) (IsLocalRing.ResidueField ↥V) := (resHom ϖ V hRV hϖV).toAlgebra
  have h𝔽surj : Function.Surjective (algebraMap R (R ⧸ (Ideal.span {ϖ} : Ideal R))) := Ideal.Quotient.mk_surjective
  have hcomp : ∀ r : R, algebraMap (R ⧸ (Ideal.span {ϖ} : Ideal R)) (IsLocalRing.ResidueField ↥V)
      (algebraMap R (R ⧸ (Ideal.span {ϖ} : Ideal R)) r) = IsLocalRing.residue ↥V ⟨algebraMap R F r, hRV r⟩ := fun r => rfl

  obtain ⟨hfinV, hfle, hb⟩ :=
    ValuationSubring.finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss R K₀ F j htj hFD hsep ϖ hϖ V hRV hϖV hjV
      (R ⧸ (Ideal.span {ϖ} : Ideal R)) h𝔽surj hcomp jV hjV'

  let kHom : R ⧸ (Ideal.span {ϖ} : Ideal R) →+* k := Ideal.Quotient.lift _ (algebraMap R k) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hk, zero_mul])
  letI algFk : Algebra (R ⧸ (Ideal.span {ϖ} : Ideal R)) k := kHom.toAlgebra
  letI algFΩ : Algebra (R ⧸ (Ideal.span {ϖ} : Ideal R)) Ω := ((algebraMap k Ω).comp kHom).toAlgebra
  haveI : IsScalarTower (R ⧸ (Ideal.span {ϖ} : Ideal R)) k Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hρker : ∀ x : ↥V, x ∈ IsLocalRing.maximalIdeal ↥V → ρ x = 0 :=
    fun x hx => hρ x (ValuationSubring.coe_mem_nonunits_iff.mpr hx)
  let ρbar₀ : IsLocalRing.ResidueField ↥V →+* Ω := Ideal.Quotient.lift _ ρ hρker
  have hρbar₀ : ∀ x : ↥V, ρbar₀ (IsLocalRing.residue ↥V x) = ρ x := fun _ => rfl
  let ρbar : IsLocalRing.ResidueField ↥V →ₐ[R ⧸ (Ideal.span {ϖ} : Ideal R)] Ω :=
    { ρbar₀ with
      commutes' := by
        intro c
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        change ρbar₀ (resHom ϖ V hRV hϖV (Ideal.Quotient.mk _ r)) = (algebraMap k Ω) (kHom (Ideal.Quotient.mk _ r))
        rw [resHom_mk]
        change ρbar₀ (IsLocalRing.residue ↥V (toV V hRV r)) = (algebraMap k Ω) (Ideal.Quotient.lift _ (algebraMap R k) _ (Ideal.Quotient.mk _ r))
        rw [hρbar₀, Ideal.Quotient.lift_mk]
        exact hρR r }
  have hρbar : ∀ x : ↥V, ρbar (IsLocalRing.residue ↥V x) = ρ x := fun _ => rfl

  letI algPoly : Algebra (R ⧸ (Ideal.span {ϖ} : Ideal R))[X] (IsLocalRing.ResidueField ↥V) :=
    (Polynomial.aeval (R := R ⧸ (Ideal.span {ϖ} : Ideal R)) (IsLocalRing.residue ↥V jV)).toRingHom.toAlgebra
  haveI : IsScalarTower (R ⧸ (Ideal.span {ϖ} : Ideal R)) (R ⧸ (Ideal.span {ϖ} : Ideal R))[X] (IsLocalRing.ResidueField ↥V) :=
    IsScalarTower.of_algebraMap_eq (fun c => by
      change algebraMap _ _ c = Polynomial.aeval (IsLocalRing.residue ↥V jV) (Polynomial.C c)
      rw [Polynomial.aeval_C])
  have hX : algebraMap (R ⧸ (Ideal.span {ϖ} : Ideal R))[X] (IsLocalRing.ResidueField ↥V) Polynomial.X = IsLocalRing.residue ↥V jV := by
    change Polynomial.aeval (IsLocalRing.residue ↥V jV) Polynomial.X = _
    rw [Polynomial.aeval_X]
  have hrange : Set.range ρbar = Set.range ρ := by
    ext y; constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact ⟨x, (hρbar₀ x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨IsLocalRing.residue ↥V x, hρbar₀ x⟩

  have hρX : ρbar (algebraMap (R ⧸ (Ideal.span {ϖ} : Ideal R))[X] (IsLocalRing.ResidueField ↥V) Polynomial.X) = (t : Ω) := by
    rw [hX, hρbar, ht]
  have htr' : Transcendental k (ρbar (algebraMap (R ⧸ (Ideal.span {ϖ} : Ideal R))[X] (IsLocalRing.ResidueField ↥V) Polynomial.X)) := by
    rw [hρX]
    exact (transcendental_algebraMap_iff (algebraMap (↥(IntermediateField.adjoin k (Set.range ρ))) Ω).injective).mpr htr

  have hfin' : FiniteDimensional
      ↥(IntermediateField.adjoin (R ⧸ (Ideal.span {ϖ} : Ideal R))
        ({algebraMap (R ⧸ (Ideal.span {ϖ} : Ideal R))[X] (IsLocalRing.ResidueField ↥V) Polynomial.X} : Set (IsLocalRing.ResidueField ↥V)))
      (IsLocalRing.ResidueField ↥V) := by
    rw [hX]; exact hfinV
  have hres := IntermediateField.finrank_adjoin_range_le_finrank_of_transcendental (R ⧸ (Ideal.span {ϖ} : Ideal R)) k
    (IsLocalRing.ResidueField ↥V) hfin' Ω ρbar htr'

  have htransport : ∀ (S : Set Ω) (hS : S = Set.range ρ) (y : Ω) (hyS : y ∈ IntermediateField.adjoin k S)
      (hyt : y = (t : Ω)),
      Module.finrank ↥(IntermediateField.adjoin k ({⟨y, hyS⟩} : Set ↥(IntermediateField.adjoin k S)))
          ↥(IntermediateField.adjoin k S) =
        Module.finrank ↥(IntermediateField.adjoin k ({t} : Set ↥(IntermediateField.adjoin k (Set.range ρ))))
          ↥(IntermediateField.adjoin k (Set.range ρ)) := by
    intro S hS y hyS hyt
    subst hS
    have hyt' : (⟨y, hyS⟩ : ↥(IntermediateField.adjoin k (Set.range ρ))) = t := Subtype.ext hyt
    rw [hyt']
  have hmemy : ρbar (algebraMap (R ⧸ (Ideal.span {ϖ} : Ideal R))[X] (IsLocalRing.ResidueField ↥V) Polynomial.X) ∈
      IntermediateField.adjoin k (Set.range ρbar) :=
    IntermediateField.subset_adjoin k (Set.range ρbar) ⟨_, rfl⟩
  have hk_eq := htransport (Set.range ρbar) hrange _ hmemy hρX
  rw [hk_eq] at hres

  have hf_eq : Module.finrank
        ↥(IntermediateField.adjoin (R ⧸ (Ideal.span {ϖ} : Ideal R))
          ({algebraMap (R ⧸ (Ideal.span {ϖ} : Ideal R))[X] (IsLocalRing.ResidueField ↥V) Polynomial.X} : Set (IsLocalRing.ResidueField ↥V)))
        (IsLocalRing.ResidueField ↥V) =
      Module.finrank
        ↥(IntermediateField.adjoin (R ⧸ (Ideal.span {ϖ} : Ideal R))
          ({IsLocalRing.residue ↥V jV} : Set (IsLocalRing.ResidueField ↥V))) (IsLocalRing.ResidueField ↥V) := by
    rw [hX]
  rw [hf_eq] at hres

  have hnf := hdeg.trans hres
  obtain ⟨hunif, huniq⟩ := hb hnf

  obtain ⟨hOV, hprime, hmem⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.span_singleton_isPrime_and_mem_iff_mem_nonunits_of_valuationSubring R K₀ F j htj hFD hsep
      ϖ hϖ V hRV hϖV hjV hunif huniq

  have hdegT := hfle.trans (hdeg.trans (le_of_eq hk_eq.symm))
  haveI hdom : IsDomain (k ⊗[R ⧸ (Ideal.span {ϖ} : Ideal R)] IsLocalRing.ResidueField ↥V) :=
    IntermediateField.isDomain_tensorProduct_of_finrank_le_finrank_adjoin_range (R ⧸ (Ideal.span {ϖ} : Ideal R)) k
      (IsLocalRing.ResidueField ↥V) hfin' Ω ρbar htr' (by rw [hf_eq]; exact hdegT)

  letI algRκV : Algebra R (IsLocalRing.ResidueField ↥V) := algRκ V hRV
  haveI towerRFκ : IsScalarTower R (R ⧸ (Ideal.span {ϖ} : Ideal R)) (IsLocalRing.ResidueField ↥V) :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI towerRFk : IsScalarTower R (R ⧸ (Ideal.span {ϖ} : Ideal R)) k :=
    IsScalarTower.of_algebraMap_eq (fun r => (Ideal.Quotient.lift_mk _ _ _).symm)
  have key : ∀ (𝒪 : Subalgebra R F) (hOV : ∀ a : ↥𝒪, (a : F) ∈ V)
      (hmem : ∀ a : ↥𝒪, a ∈ Ideal.span {algebraMap R ↥𝒪 ϖ} ↔ (a : F) ∈ V.nonunits),
      IsDomain (k ⊗[R] ↥𝒪) := by
    intro 𝒪 hOV hmem

    let ψ : ↥𝒪 →ₐ[R] IsLocalRing.ResidueField ↥V := redHom V hRV 𝒪 hOV
    have hψ : ∀ a : ↥𝒪, ψ a = IsLocalRing.residue ↥V ⟨a, hOV a⟩ := fun _ => rfl
    have hψker : ∀ a : ↥𝒪, ψ a = 0 ↔ a ∈ Ideal.span {algebraMap R ↥𝒪 ϖ} := by
      intro a
      rw [hψ, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff, hmem a]
    obtain ⟨I, hI⟩ : ∃ I : Ideal ↥𝒪, I = Ideal.span {algebraMap R ↥𝒪 ϖ} := ⟨_, rfl⟩

    have hle : (Ideal.span {ϖ} : Ideal R) ≤ I.comap (algebraMap R ↥𝒪) := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hI]
      exact Ideal.subset_span rfl
    letI algFQ : Algebra (R ⧸ (Ideal.span {ϖ} : Ideal R)) (↥𝒪 ⧸ I) := (Ideal.quotientMap I (algebraMap R ↥𝒪) hle).toAlgebra
    haveI towerRFQ : IsScalarTower R (R ⧸ (Ideal.span {ϖ} : Ideal R)) (↥𝒪 ⧸ I) :=
      IsScalarTower.of_algebraMap_eq (fun r => by
        change algebraMap R (↥𝒪 ⧸ I) r = Ideal.quotientMap I (algebraMap R ↥𝒪) hle (Ideal.Quotient.mk _ r)
        rw [Ideal.quotientMap_mk]
        rfl)

    let φR : (↥𝒪 ⧸ I) →ₐ[R] IsLocalRing.ResidueField ↥V :=
      Ideal.Quotient.liftₐ I ψ (fun a ha => (hψker a).2 (hI ▸ ha))
    have hφR : ∀ a : ↥𝒪, φR (Ideal.Quotient.mk I a) = ψ a := fun _ => rfl
    have hφinj : Function.Injective φR := by
      intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hφR, hφR, ← sub_eq_zero, ← map_sub, hψker] at hxy
      rw [Ideal.Quotient.eq, hI]
      exact hxy
    let φ : (↥𝒪 ⧸ I) →ₐ[R ⧸ (Ideal.span {ϖ} : Ideal R)] IsLocalRing.ResidueField ↥V :=
      { φR.toRingHom with
        commutes' := by
          intro c
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
          change φR (algebraMap R (↥𝒪 ⧸ I) r) = algebraMap R (IsLocalRing.ResidueField ↥V) r
          exact φR.commutes r }
    have hφ : Function.Injective φ := hφinj

    let G₁ : k ⊗[R] ↥𝒪 →ₐ[R] k ⊗[R] (↥𝒪 ⧸ I) := Algebra.TensorProduct.map (AlgHom.id R k) (Ideal.Quotient.mkₐ R I)
    have hG₁ : Function.Injective G₁ := by
      rw [RingHom.injective_iff_ker_eq_bot]
      change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R k) (Ideal.Quotient.mkₐ R I)) = ⊥
      rw [Algebra.TensorProduct.lTensor_ker _ (Ideal.Quotient.mkₐ_surjective R I),
        show RingHom.ker (Ideal.Quotient.mkₐ R I) = I from Ideal.Quotient.mkₐ_ker R I, hI,
        Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_bot]
      change (1 : k) ⊗ₜ[R] (algebraMap R ↥𝒪 ϖ) = 0
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, hk,
        TensorProduct.zero_tmul]

    let G₂ : k ⊗[R ⧸ (Ideal.span {ϖ} : Ideal R)] (↥𝒪 ⧸ I) →ₐ[R ⧸ (Ideal.span {ϖ} : Ideal R)]
        k ⊗[R ⧸ (Ideal.span {ϖ} : Ideal R)] IsLocalRing.ResidueField ↥V :=
      Algebra.TensorProduct.map (AlgHom.id _ k) φ
    have hG₂ : Function.Injective G₂ := by
      have : G₂.toLinearMap = LinearMap.lTensor k φ.toLinearMap := by
        apply TensorProduct.ext'
        intro a b
        rfl
      have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := k) φ.toLinearMap hφ
      intro x y hxy
      apply h2
      change (LinearMap.lTensor k φ.toLinearMap) x = (LinearMap.lTensor k φ.toLinearMap) y
      rw [← this]
      exact hxy

    haveI : TensorProduct.CompatibleSMul R (R ⧸ (Ideal.span {ϖ} : Ideal R)) k (↥𝒪 ⧸ I) :=
      TensorProduct.CompatibleSMul.of_algebraMap_surjective k (↥𝒪 ⧸ I) h𝔽surj
    let E₁ : k ⊗[R ⧸ (Ideal.span {ϖ} : Ideal R)] (↥𝒪 ⧸ I) ≃ₐ[R] k ⊗[R] (↥𝒪 ⧸ I) :=
      Algebra.TensorProduct.equivOfCompatibleSMul R (R ⧸ (Ideal.span {ϖ} : Ideal R)) R k (↥𝒪 ⧸ I)

    let Gtot : k ⊗[R] ↥𝒪 →+* k ⊗[R ⧸ (Ideal.span {ϖ} : Ideal R)] IsLocalRing.ResidueField ↥V :=
      G₂.toRingHom.comp (E₁.symm.toRingEquiv.toRingHom.comp G₁.toRingHom)
    have hGtot : Function.Injective Gtot := hG₂.comp (E₁.symm.injective.comp hG₁)
    exact Function.Injective.isDomain Gtot hGtot

  refine ⟨key _ hOV hmem, ?_, ?_⟩
  ·
    haveI : Fact (j⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : j ≠ 0)⟩
    have hjVi := DeuringAsmH.gaussType_inv hϖ.not_unit (Fact.out : j ≠ 0) V hjV
    have htji : Transcendental R j⁻¹ := DeuringAsmH.transcendental_inv htj
    have hFDi : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by
      rw [DeuringAsmH.adjoin_inv_eq]; exact hFD
    have hsepi : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by
      rw [DeuringAsmH.adjoin_inv_eq]; exact hsep
    have huniqi : ∀ V' : ValuationSubring F, (∀ r : R, algebraMap R F r ∈ V') → algebraMap R F ϖ ∈ V'.nonunits →
        (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j⁻¹ P ∈ V' ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V') →
        V' = V := by
      intro V' h1 h2 h3
      refine huniq V' h1 h2 ?_
      have h4 := DeuringAsmH.gaussType_inv hϖ.not_unit (inv_ne_zero (Fact.out : j ≠ 0)) V' h3
      rw [inv_inv j] at h4
      exact h4
    obtain ⟨hOVi, -, hmemi⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.span_singleton_isPrime_and_mem_iff_mem_nonunits_of_valuationSubring R K₀ F j⁻¹ htji
        hFDi hsepi ϖ hϖ V hRV hϖV hjVi hunif huniqi
    exact key (TwoChartIntegralModel.chartAlgInf R F j) hOVi hmemi
  ·
    have hXnd : ¬ (Polynomial.C ϖ ∣ (Polynomial.X : R[X])) := by
      rintro ⟨Q, hQ⟩
      have h1 : (Polynomial.X : R[X]).coeff 1 = ϖ * Q.coeff 1 := by rw [hQ, Polynomial.coeff_C_mul]
      rw [Polynomial.coeff_X_one] at h1
      exact hϖ.not_unit (isUnit_iff_exists_inv.mpr ⟨Q.coeff 1, h1.symm⟩)
    have hjW := hjV Polynomial.X hXnd
    rw [Polynomial.aeval_X] at hjW
    have hOVm : ∀ a : ↥(TwoChartIntegralModel.chartAlgMid R F j), (a : F) ∈ V :=
      DeuringAsmH.chartAlgMid_le R F j V hRV hjW.1 hjW.2
    let ψm : ↥(TwoChartIntegralModel.chartAlgMid R F j) →ₐ[R] IsLocalRing.ResidueField ↥V :=
      redHom V hRV (TwoChartIntegralModel.chartAlgMid R F j) hOVm
    haveI : TensorProduct.CompatibleSMul R (R ⧸ (Ideal.span {ϖ} : Ideal R)) k (IsLocalRing.ResidueField ↥V) :=
      TensorProduct.CompatibleSMul.of_algebraMap_surjective k (IsLocalRing.ResidueField ↥V) h𝔽surj
    haveI : Nontrivial (k ⊗[R] IsLocalRing.ResidueField ↥V) :=
      (Algebra.TensorProduct.equivOfCompatibleSMul R (R ⧸ (Ideal.span {ϖ} : Ideal R)) R k
        (IsLocalRing.ResidueField ↥V)).symm.toEquiv.nontrivial
    exact (Algebra.TensorProduct.map (AlgHom.id R k) ψm).toRingHom.domain_nontrivial

end S_AlgebraicCurve_TwoChartIntegralModel_isDomain_tensorProduct_chartAlg_of_finrank_le_finrank_adjoin_range
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isDomain_tensorProduct_chartAlg_of_finrank_le_finrank_adjoin_range (solution)
