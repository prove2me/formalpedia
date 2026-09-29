-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/bee7bdc5-42eb-5a3b-b4bf-707b1e0f793f

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace BDescCS5

theorem isUnit_of_inv_mem {L : Type u} [Field L] (B : Subring L) (x : L) (hx : x ∈ B) (hxi : x⁻¹ ∈ B) (hx0 : x ≠ 0) :
    IsUnit (⟨x, hx⟩ : ↥B) :=
  ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hxi⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem inv_mem_of_isUnit {L : Type u} [Field L] (B : Subring L) (x : ↥B) (hx : IsUnit x) : ((x : L))⁻¹ ∈ B := by
  obtain ⟨u, rfl⟩ := hx
  have h : ((u : ↥B) : L) * (((u⁻¹ : (↥B)ˣ) : ↥B) : L) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rw [inv_eq_of_mul_eq_one_right h]
  exact ((u⁻¹ : (↥B)ˣ) : ↥B).2

end BDescCS5

open BDescCS5 in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)]
    (𝔮 : Ideal ↥(chartAlgFin R F f)) [𝔮.IsPrime] (hϖ𝔮 : algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔮)
    (𝔪 : Ideal ↥(chartAlgFin R F f)) (h𝔪 : 𝔪.IsMaximal) (h𝔮𝔪 : 𝔮 ≤ 𝔪)
    (t : ↥(chartAlgFin R F f)) (ht : t ∈ 𝔪) (ht𝔮 : t ∉ 𝔮)
    (n : ℕ) (hn : 1 ≤ n) (g : F)
    (hg : ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 ∧ g * (c : F) = (b : F))
    (h3 : ∃ b c : ↥(chartAlgFin R F f), b ∉ 𝔪 ∧ c ∉ 𝔪 ∧ g * (t : F) ^ n * (c : F) = (b : F))
    (O : ValuationSubring F)
    (hO : ∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 ∧ y * (c : F) = (b : F)) :
    ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O := by
  classical
  intro P hP
  haveI h𝔪p : 𝔪.IsPrime := h𝔪.isPrime
  have h𝔮top : 𝔮 ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance

  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hAinj : Function.Injective (algebraMap R ↥(chartAlgFin R F f)) := by
    intro x y h
    apply hRF
    have := congrArg (fun z : ↥(chartAlgFin R F f) => (z : F)) h
    simpa only [Subalgebra.coe_algebraMap] using this

  have hAO : ∀ a : ↥(chartAlgFin R F f), (a : F) ∈ O := fun a =>
    (hO a).mpr ⟨a, 1, fun h => h𝔮top ((Ideal.eq_top_iff_one _).mpr h), by rw [OneMemClass.coe_one, mul_one]⟩
  have hne0 : ∀ a : ↥(chartAlgFin R F f), a ∉ 𝔮 → (a : F) ≠ 0 := by
    intro a ha h0
    apply ha
    have : a = 0 := Subtype.ext h0
    rw [this]; exact Ideal.zero_mem _
  have hinvO : ∀ a : ↥(chartAlgFin R F f), a ∉ 𝔮 → ((a : F))⁻¹ ∈ O := fun a ha =>
    (hO _).mpr ⟨1, a, ha, by rw [inv_mul_cancel₀ (hne0 a ha), OneMemClass.coe_one]⟩
  have hmaxO : ∀ a : ↥(chartAlgFin R F f), a ∈ 𝔮 → (⟨(a : F), hAO a⟩ : ↥O) ∈ maximalIdeal ↥O := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    by_cases ha0 : (a : F) = 0
    · apply hu.ne_zero
      exact Subtype.ext ha0
    have hi : ((a : F))⁻¹ ∈ O := inv_mem_of_isUnit O.toSubring ⟨(a : F), hAO a⟩ hu
    obtain ⟨b, c, hc, hbc⟩ := (hO _).mp hi
    apply hc
    have hcab : (c : F) = (a : F) * (b : F) := by
      rw [← hbc, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    have : c = a * b := Subtype.ext (by rw [Subalgebra.coe_mul]; exact hcab)
    rw [this]
    exact Ideal.mul_mem_right _ _ ha

  have hgO : g ∈ O := (hO g).mpr hg
  let gO : ↥O := ⟨g, hgO⟩
  let φR : R →+* ↥O := (algebraMap R F).codRestrict O.toSubring (fun r => by
    have := hAO (algebraMap R ↥(chartAlgFin R F f) r)
    rwa [Subalgebra.coe_algebraMap] at this)
  have hφR : ∀ r : R, ((φR r : ↥O) : F) = algebraMap R F r := fun r => rfl
  have hPgO : Polynomial.aeval g P = ((P.eval₂ φR gO : ↥O) : F) := by
    rw [Polynomial.aeval_def]
    show P.eval₂ (algebraMap R F) g = O.subtype (P.eval₂ φR gO)
    rw [Polynomial.hom_eval₂]
    rfl
  refine ⟨by rw [hPgO]; exact (P.eval₂ φR gO).2, ?_⟩
  suffices hunit : IsUnit (P.eval₂ φR gO) by
    rw [hPgO]; exact inv_mem_of_isUnit O.toSubring _ hunit
  by_contra hnu
  have hzero : IsLocalRing.residue ↥O (P.eval₂ φR gO) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hnu
  rw [Polynomial.hom_eval₂] at hzero

  let φA : ↥(chartAlgFin R F f) →+* ResidueField ↥O :=
    (IsLocalRing.residue ↥O).comp
      { toFun := fun a => ⟨(a : F), hAO a⟩
        map_one' := Subtype.ext (by rw [OneMemClass.coe_one]; rfl)
        map_mul' := fun x y => Subtype.ext (by rw [Subalgebra.coe_mul]; rfl)
        map_zero' := Subtype.ext (by rw [ZeroMemClass.coe_zero]; rfl)
        map_add' := fun x y => Subtype.ext (by rw [Subalgebra.coe_add]; rfl) }
  have hφA : ∀ a, φA a = IsLocalRing.residue ↥O ⟨(a : F), hAO a⟩ := fun a => rfl
  have hφA0 : ∀ a, a ∈ 𝔮 → φA a = 0 := fun a ha => by
    rw [hφA, IsLocalRing.residue_eq_zero_iff]; exact hmaxO a ha
  have hφAne : ∀ a, a ∉ 𝔮 → φA a ≠ 0 := by
    intro a ha h
    rw [hφA, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
    exact h (isUnit_of_inv_mem O.toSubring (a : F) (hAO a) (hinvO a ha) (hne0 a ha))
  have hφR_A : ∀ r : R, (IsLocalRing.residue ↥O).comp φR r = φA (algebraMap R ↥(chartAlgFin R F f) r) := by
    intro r
    rw [RingHom.comp_apply, hφA]
    congr 1

  have hunitsκ : ∀ y : 𝔪.primeCompl, IsUnit (φA y) := fun y =>
    IsUnit.mk0 _ (hφAne y (fun h => y.2 (h𝔮𝔪 h)))
  let fL : Localization.AtPrime 𝔪 →+* ResidueField ↥O :=
    IsLocalization.lift (M := 𝔪.primeCompl) (S := Localization.AtPrime 𝔪) hunitsκ
  have hfL : ∀ a, fL (algebraMap _ (Localization.AtPrime 𝔪) a) = φA a := fun a =>
    IsLocalization.lift_eq hunitsκ a
  obtain ⟨W, hW, hWloc⟩ := IsLocalRing.exists_factor_valuationRing fL
  have hφAW : ∀ a, φA a ∈ W := fun a => by
    have := hW (algebraMap _ (Localization.AtPrime 𝔪) a)
    rw [hfL] at this
    exact this
  have hunitW : ∀ a, a ∉ 𝔪 → IsUnit (⟨φA a, hφAW a⟩ : ↥W) := by
    intro a ha
    have hu : IsUnit (algebraMap _ (Localization.AtPrime 𝔪) a) :=
      IsLocalization.map_units (Localization.AtPrime 𝔪) (⟨a, ha⟩ : 𝔪.primeCompl)
    have hu' := hu.map (fL.codRestrict W.toSubring hW)
    have heq : (fL.codRestrict W.toSubring hW) (algebraMap _ (Localization.AtPrime 𝔪) a) = ⟨φA a, hφAW a⟩ :=
      Subtype.ext (hfL a)
    rw [heq] at hu'
    exact hu'
  have hnonunitW : ∀ a, a ∈ 𝔪 → ¬ IsUnit (⟨φA a, hφAW a⟩ : ↥W) := by
    intro a ha hu
    have heq : (fL.codRestrict W.toSubring hW) (algebraMap _ (Localization.AtPrime 𝔪) a) = ⟨φA a, hφAW a⟩ :=
      Subtype.ext (hfL a)
    rw [← heq] at hu
    have := hWloc.map_nonunit _ hu
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔪) 𝔪 a] at this
    exact this ha

  set gbar : ResidueField ↥O := IsLocalRing.residue ↥O gO with hgbar
  obtain ⟨b, c, hb, hc, hgtc⟩ := h3
  have hgbartc : gbar * (φA t) ^ n * φA c = φA b := by
    have h1 : gO * (⟨(t : F), hAO t⟩ : ↥O) ^ n * ⟨(c : F), hAO c⟩ = ⟨(b : F), hAO b⟩ :=
      Subtype.ext (by simp only [Subring.coe_mul, Subring.coe_pow] at hgtc ⊢; exact hgtc)
    have h2 := congrArg (IsLocalRing.residue ↥O) h1
    rw [map_mul, map_mul, map_pow] at h2
    rw [hgbar, hφA, hφA, hφA]
    exact h2
  have hgbarW : gbar ∉ W := by
    intro hgbarW
    apply hnonunitW t ht
    have hprod : (⟨gbar, hgbarW⟩ : ↥W) * ⟨φA t, hφAW t⟩ ^ n * ⟨φA c, hφAW c⟩ = ⟨φA b, hφAW b⟩ :=
      Subtype.ext (by simp only [Subring.coe_mul, Subring.coe_pow] at hgbartc ⊢; exact hgbartc)
    have hub : IsUnit ((⟨gbar, hgbarW⟩ : ↥W) * ⟨φA t, hφAW t⟩ ^ n * ⟨φA c, hφAW c⟩) := by
      rw [hprod]; exact hunitW b hb
    have hn0 : n ≠ 0 := by omega
    exact (isUnit_pow_iff hn0).mp (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hub))

  have hvg : 1 < W.valuation gbar := by
    rw [← not_le, W.valuation_le_one_iff]; exact hgbarW
  have hcoef0 : ∀ i, ϖ ∣ P.coeff i → (IsLocalRing.residue ↥O).comp φR (P.coeff i) = 0 := by
    rintro i ⟨r, hr⟩
    rw [hr, map_mul, hφR_A ϖ, hφA0 _ hϖ𝔮, zero_mul]
  have hcoef1 : ∀ i, ¬ ϖ ∣ P.coeff i → W.valuation ((IsLocalRing.residue ↥O).comp φR (P.coeff i)) = 1 := by
    intro i hi
    have hu : IsUnit (P.coeff i) := by
      by_contra hnu'
      apply hi
      have : P.coeff i ∈ maximalIdeal R := hnu'
      rw [hϖ, Ideal.mem_span_singleton] at this
      exact this
    rw [hφR_A]
    have hu' : IsUnit (⟨φA (algebraMap R _ (P.coeff i)), hφAW _⟩ : ↥W) := by
      obtain ⟨w, hw⟩ := hu
      refine ⟨⟨⟨φA (algebraMap R _ (P.coeff i)), hφAW _⟩, ⟨φA (algebraMap R _ (w⁻¹ : Rˣ)), hφAW _⟩,
        Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
      · show φA _ * φA _ = 1
        rw [← map_mul, ← map_mul, ← hw, Units.mul_inv, map_one, map_one]
      · show φA _ * φA _ = 1
        rw [← map_mul, ← map_mul, ← hw, Units.inv_mul, map_one, map_one]
    exact (W.valuation_eq_one_iff _).mp hu'

  have hex : ((Finset.range (P.natDegree + 1)).filter (fun i => ¬ ϖ ∣ P.coeff i)).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hempty
    apply hP
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi : i < P.natDegree + 1
    · exact not_not.mp (hempty (Finset.mem_range.mpr hi))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _
  set m := ((Finset.range (P.natDegree + 1)).filter (fun i => ¬ ϖ ∣ P.coeff i)).max' hex with hm
  have hmmem := Finset.max'_mem _ hex
  rw [← hm, Finset.mem_filter] at hmmem
  obtain ⟨hmrange, hmunit⟩ := hmmem
  rw [Polynomial.eval₂_eq_sum_range] at hzero
  have key := Valuation.map_sum_eq_of_lt W.valuation (s := Finset.range (P.natDegree + 1))
    (f := fun i => (IsLocalRing.residue ↥O).comp φR (P.coeff i) * gbar ^ i) (j := m) hmrange ?_
  · rw [hzero, map_zero, map_mul, map_pow, hcoef1 m hmunit, one_mul] at key
    exact absurd key.symm (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hvg)))
  · intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    obtain ⟨hirange, hine⟩ := hi
    rw [map_mul, map_mul, map_pow, map_pow, hcoef1 m hmunit, one_mul]
    by_cases hdiv : ϖ ∣ P.coeff i
    · rw [hcoef0 i hdiv, map_zero, zero_mul]
      exact pow_pos (lt_trans zero_lt_one hvg) _
    · rw [hcoef1 i hdiv, one_mul]
      have hile : i ≤ m := by
        rw [hm]; exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hirange, hdiv⟩)
      exact pow_lt_pow_right₀ hvg (lt_of_le_of_ne hile hine)

end S_AlgebraicCurve_TwoChartIntegralModel_forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal (solution)
