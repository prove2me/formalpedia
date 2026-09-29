-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/55a69675-15ee-519c-981f-8531b14d35bc

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ValuationSubring_inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_jInvChartInf_not_mem_of_mem_minimalPrimes_span
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_not_forall_aeval_mem_and_inv_mem_of_forall_lt_of_forall_jInvChartInf_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization

set_option autoImplicit false

universe u

p2m_open "IsLocalRing AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization.AlgebraicCurve.TwoChartIntegralModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "mem_chartAlg_iff chartAlgFin chartAlgInf jChartFin jInvChartInf mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin finiteType_chartAlgFin_and_chartAlgInf jInvChartInf_not_mem_of_mem_minimalPrimes_span forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal not_forall_aeval_mem_and_inv_mem_of_forall_lt_of_forall_jInvChartInf_mem"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

namespace CompSupport

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F : Type u) [Field F] [Algebra R F]

theorem chartAlgFin_le (j : F) [Fact (j ≠ 0)] (O : ValuationSubring F)
    (hRO : ∀ a : R, algebraMap R F a ∈ O) (hjO : j ∈ O) :
    ∀ x : ↥(chartAlgFin R F j), (x : F) ∈ O := by
  intro x

  have hadjO : ∀ y : F, y ∈ Algebra.adjoin R ({j} : Set F) → y ∈ O := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff] at hz; exact hz ▸ hjO
    | algebraMap r => exact hRO r
    | add a b _ _ ha hb => exact O.add_mem _ _ ha hb
    | mul a b _ _ ha hb => exact O.mul_mem _ _ ha hb
  let φ : ↥(Algebra.adjoin R ({j} : Set F)) →+* ↥O :=
    { toFun := fun y => ⟨(y : F), hadjO y y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  letI : Algebra ↥(Algebra.adjoin R ({j} : Set F)) ↥O := φ.toAlgebra
  haveI : IsScalarTower ↥(Algebra.adjoin R ({j} : Set F)) ↥O F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hx : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) (x : F) := (mem_chartAlg_iff R F).mp x.2
  have hxO : IsIntegral ↥O (x : F) := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥O) (K := F)).mp hxO
  rw [← hy]
  exact y.2

theorem exists_centre (ϖ : R) (A : Subalgebra R F) (O : ValuationSubring F)
    (hAO : ∀ x : ↥A, (x : F) ∈ O) (hϖO : algebraMap R F ϖ ∈ O.nonunits) :
    ∃ 𝔭 : Ideal ↥A, 𝔭.IsPrime ∧ algebraMap R ↥A ϖ ∈ 𝔭 ∧
      (∀ x : ↥A, x ∈ 𝔭 ↔ (x : F) ∈ O.nonunits) ∧
      (∀ b c : ↥A, c ∉ 𝔭 → (b : F) * (c : F)⁻¹ ∈ O) := by
  classical
  let toO : ↥A →+* ↥O := (A.val.toRingHom).codRestrict O.toSubring (fun x => hAO x)
  let 𝔭 : Ideal ↥A := (maximalIdeal ↥O).comap toO
  have hmem : ∀ x : ↥A, x ∈ 𝔭 ↔ (x : F) ∈ O.nonunits := by
    intro x
    rw [Ideal.mem_comap]
    exact (ValuationSubring.coe_mem_nonunits_iff (A := O) (a := toO x)).symm
  refine ⟨𝔭, Ideal.comap_isPrime toO _, ?_, hmem, ?_⟩
  · rw [hmem]; simpa [Subalgebra.algebraMap_def] using hϖO
  · intro b c hc
    have hcu : IsUnit (⟨(c : F), hAO c⟩ : ↥O) := by
      by_contra hu
      exact hc ((hmem c).2 ((ValuationSubring.coe_mem_nonunits_iff (A := O) (a := ⟨_, hAO c⟩)).2
        ((mem_maximalIdeal _).2 hu)))
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hcu
    have hwval : (w : F) = (c : F)⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)
    rw [← hwval]
    exact O.mul_mem _ _ (hAO b) w.2

theorem isUnit_aeval_of_gauss (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ}) (O : ValuationSubring F)
    (hϖO : algebraMap R F ϖ ∈ O.nonunits) (hϖ0 : algebraMap R F ϖ ≠ 0) (g : F)
    (hgauss : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O) :
    ∀ p : Polynomial R, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ (algebraMap R F) g p ∈ O, IsUnit (⟨_, hO⟩ : ↥O) := by
  classical
  have hϖnu : ¬ IsUnit ϖ := by
    have : ϖ ∈ maximalIdeal R := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
    exact (IsLocalRing.mem_maximalIdeal _).mp this
  have hndvd : ∀ p : Polynomial R, (∃ i, IsUnit (p.coeff i)) → ¬ (Polynomial.C ϖ ∣ p) := by
    rintro p ⟨i, hi⟩ ⟨q, rfl⟩
    rw [Polynomial.coeff_C_mul] at hi
    exact hϖnu (isUnit_of_mul_isUnit_left hi)
  intro p hp
  obtain ⟨hmem, hinv⟩ := hgauss p (hndvd p hp)
  rw [Polynomial.aeval_def] at hmem hinv
  refine ⟨hmem, ?_⟩

  have hne : Polynomial.eval₂ (algebraMap R F) g p ≠ 0 := by
    intro h0
    have hp' : ∃ i, IsUnit ((p + Polynomial.C ϖ).coeff i) := by
      obtain ⟨i, hi⟩ := hp
      refine ⟨i, ?_⟩
      rw [Polynomial.coeff_add, Polynomial.coeff_C]
      split_ifs with hi0
      · by_contra hu
        have h1 : p.coeff i + ϖ ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hu
        have h2 : ϖ ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hϖnu
        have h3 : p.coeff i ∈ maximalIdeal R := by
          have := (maximalIdeal R).sub_mem h1 h2
          rwa [add_sub_cancel_right] at this
        exact (IsLocalRing.mem_maximalIdeal _).1 h3 hi
      · rwa [add_zero]
    obtain ⟨-, hinv'⟩ := hgauss _ (hndvd _ hp')
    rw [Polynomial.aeval_def, Polynomial.eval₂_add, h0, zero_add, Polynomial.eval₂_C] at hinv'
    rw [ValuationSubring.mem_nonunits_iff_or] at hϖO
    rcases hϖO with h | h
    · exact hϖ0 h
    · exact h hinv'
  exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : ↥O) (by ext; simp [mul_inv_cancel₀ hne])

theorem not_gauss_of_isMaximal_centre (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ}) (hϖ0 : algebraMap R F ϖ ≠ 0)
    (A : Subalgebra R F) [Algebra.FiniteType R ↥A]
    (O : ValuationSubring F) (hAO : ∀ x : ↥A, (x : F) ∈ O) (hϖO : algebraMap R F ϖ ∈ O.nonunits)
    (𝔪 : Ideal ↥A) (h𝔪 : 𝔪.IsMaximal) (hcen : ∀ x : ↥A, x ∈ 𝔪 ↔ (x : F) ∈ O.nonunits)
    (g : F) (hg : ∃ b c : ↥A, c ∉ 𝔪 ∧ g * (c : F) = (b : F)) :
    ¬ ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O := by
  classical
  intro hgauss
  have hunit := isUnit_aeval_of_gauss R F ϖ hϖ O hϖO hϖ0 g hgauss
  have hgO : g ∈ O := by
    obtain ⟨h, -⟩ := hunit Polynomial.X ⟨1, by simp⟩
    simpa using h
  obtain ⟨b, c, hc, hgc⟩ := hg

  let κ := ↥A ⧸ 𝔪
  letI : Field κ := Ideal.Quotient.field 𝔪
  let π : ↥A →+* κ := Ideal.Quotient.mk 𝔪
  have hϖ𝔪 : algebraMap R ↥A ϖ ∈ 𝔪 := by rw [hcen, Subalgebra.coe_algebraMap]; exact hϖO
  let k := R ⧸ maximalIdeal R
  letI : Field k := Ideal.Quotient.field (maximalIdeal R)
  have hker : ∀ r ∈ maximalIdeal R, π (algebraMap R ↥A r) = 0 := by
    intro r hr
    rw [hϖ, Ideal.mem_span_singleton] at hr
    obtain ⟨s, rfl⟩ := hr
    rw [map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 hϖ𝔪, zero_mul]
  let ι : k →+* κ := Ideal.Quotient.lift (maximalIdeal R) (π.comp (algebraMap R ↥A)) hker
  letI algkκ : Algebra k κ := ι.toAlgebra
  haveI : IsScalarTower R k κ := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Algebra.FiniteType k κ := Algebra.FiniteType.of_restrictScalars_finiteType R k κ
  haveI : Module.Finite k κ := finite_of_finite_type_of_isJacobsonRing k κ

  have hπc : π c ≠ 0 := fun h => hc (Ideal.Quotient.eq_zero_iff_mem.1 h)
  let gbar : κ := π b * (π c)⁻¹
  have hint : IsIntegral k gbar := Algebra.IsIntegral.isIntegral gbar
  obtain ⟨p, hpmonic, hpeval⟩ := hint

  have hsurj : Function.Surjective (algebraMap R k) := Ideal.Quotient.mk_surjective
  have hlifts : p ∈ Polynomial.lifts (algebraMap R k) :=
    (Polynomial.lifts_iff_coeff_lifts p).mpr fun i => hsurj _
  obtain ⟨P, hPp, -, hPmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hpmonic

  let toO : ↥A →+* ↥O := (A.val.toRingHom).codRestrict O.toSubring (fun x => hAO x)
  have hkerO : ∀ a ∈ 𝔪, (IsLocalRing.residue ↥O) (toO a) = 0 := by
    intro a ha
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (ValuationSubring.coe_mem_nonunits_iff (A := O) (a := toO a)).1 ((hcen a).1 ha)
  let ψ : κ →+* IsLocalRing.ResidueField ↥O := Ideal.Quotient.lift 𝔪 ((IsLocalRing.residue ↥O).comp toO) hkerO

  let gO : ↥O := ⟨g, hgO⟩
  have hcOu : IsUnit (toO c) := by
    by_contra hu
    exact hc ((hcen c).2 ((ValuationSubring.coe_mem_nonunits_iff (A := O) (a := toO c)).2
      ((mem_maximalIdeal _).2 hu)))
  have hgO_eq : gO * toO c = toO b := Subtype.ext hgc
  have hψg : ψ gbar = IsLocalRing.residue ↥O gO := by
    have h1 : ψ (π b) = IsLocalRing.residue ↥O (toO b) := Ideal.Quotient.lift_mk _ _ _
    have h2 : ψ (π c) = IsLocalRing.residue ↥O (toO c) := Ideal.Quotient.lift_mk _ _ _
    have hcres : IsLocalRing.residue ↥O (toO c) ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff]; exact fun h => (mem_maximalIdeal _).1 h hcOu
    have : IsLocalRing.residue ↥O gO * IsLocalRing.residue ↥O (toO c) = IsLocalRing.residue ↥O (toO b) := by
      rw [← map_mul, hgO_eq]
    rw [show gbar = π b * (π c)⁻¹ from rfl, map_mul, map_inv₀, h1, h2, ← this, mul_inv_cancel_right₀ hcres]

  have hφ : ψ.comp (ι.comp (algebraMap R k)) = (IsLocalRing.residue ↥O).comp (toO.comp (algebraMap R ↥A)) := by
    ext r
    rfl
  have hres0 : IsLocalRing.residue ↥O (Polynomial.eval₂ (toO.comp (algebraMap R ↥A)) gO P) = 0 := by
    have e1 : Polynomial.eval₂ (ι.comp (algebraMap R k)) gbar P = 0 := by
      have := hpeval
      rw [← hPp, Polynomial.eval₂_map] at this
      exact this
    have e2 := congrArg ψ e1
    rw [Polynomial.hom_eval₂, map_zero, hψg, hφ] at e2
    rw [Polynomial.hom_eval₂]
    exact e2

  obtain ⟨hPO, hPu⟩ := hunit P ⟨P.natDegree, by rw [hPmonic.coeff_natDegree]; exact isUnit_one⟩
  have heq : (⟨Polynomial.eval₂ (algebraMap R F) g P, hPO⟩ : ↥O) = Polynomial.eval₂ (toO.comp (algebraMap R ↥A)) gO P := by
    apply Subtype.ext
    change Polynomial.eval₂ (algebraMap R F) g P = (O.subtype) (Polynomial.eval₂ (toO.comp (algebraMap R ↥A)) gO P)
    rw [Polynomial.hom_eval₂]
    congr 1
  rw [heq] at hPu
  rw [IsLocalRing.residue_eq_zero_iff] at hres0
  exact (mem_maximalIdeal _).1 hres0 hPu

theorem not_mem_of_mul_pow_mul_eq (A : Subalgebra R F) (O : ValuationSubring F)
    (hAO : ∀ x : ↥A, (x : F) ∈ O)
    (𝔪 : Ideal ↥A) (hcen : ∀ x : ↥A, x ∈ 𝔪 ↔ (x : F) ∈ O.nonunits)
    (t : ↥A) (ht : t ∈ 𝔪) (n : ℕ) (hn : 1 ≤ n) (g : F)
    (h3 : ∃ b c : ↥A, b ∉ 𝔪 ∧ c ∉ 𝔪 ∧ g * (t : F) ^ n * (c : F) = (b : F)) :
    g ∉ O := by
  intro hgO
  obtain ⟨b, c, hb, hc, h⟩ := h3
  apply hb
  rw [hcen, ValuationSubring.coe_mem_nonunits_iff (A := O) (a := ⟨_, hAO b⟩)]
  have ht' : (⟨(t : F), hAO t⟩ : ↥O) ∈ maximalIdeal ↥O :=
    (ValuationSubring.coe_mem_nonunits_iff (A := O) (a := ⟨_, hAO t⟩)).1 ((hcen t).1 ht)
  have hprod : (⟨(b : F), hAO b⟩ : ↥O) = (⟨g, hgO⟩ * ⟨(c : F), hAO c⟩) * ⟨(t : F), hAO t⟩ ^ n := by
    apply Subtype.ext
    change (b : F) = g * (c : F) * (t : F) ^ n
    rw [← h]; ring
  rw [hprod]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [pow_succ, ← mul_assoc]
  exact Ideal.mul_mem_left _ _ ht'

theorem exists_valuationSubring_forall_mem_iff_and_eq (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (𝔮 : Ideal ↥(chartAlgFin R F f))
    (h𝔮 : 𝔮 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes) :
    ∃ V : ValuationSubring F,
      (∀ y : F, y ∈ V ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 ∧ y * (c : F) = (b : F)) ∧
      (∀ a : R, algebraMap R F a ∈ V) ∧ algebraMap R F ϖ ∈ V.nonunits ∧
      ∀ O : ValuationSubring F, (∀ x : ↥(chartAlgFin R F f), (x : F) ∈ O) →
        (∀ x : ↥(chartAlgFin R F f), x ∈ 𝔮 ↔ (x : F) ∈ O.nonunits) → O = V := by
  classical
  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hϖprime : Prime ϖ := ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ).prime
  have hϖ0 : algebraMap R F ϖ ≠ 0 := (map_ne_zero_iff _ hRF).2 hϖprime.ne_zero
  obtain ⟨V, -, hAV, hcenV, hϖV, hgaussV⟩ :=
    exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin R K₀ F f htf hFD hsep ϖ hϖprime 𝔮 h𝔮
  have hRV : ∀ a : R, algebraMap R F a ∈ V := fun a => by
    have := hAV (algebraMap R ↥(chartAlgFin R F f) a)
    rwa [Subalgebra.coe_algebraMap] at this
  have hfV : f ∈ V := hAV (jChartFin R F f)
  have hgeo := isUnit_aeval_of_gauss R F ϖ hϖ V hϖV hϖ0 f hgaussV
  obtain ⟨-, -, -, -, -, -, hrest⟩ :=
    ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
      R ϖ hϖ K₀ F V hRV hϖV f hfV hgeo
  obtain ⟨-, 𝔭, -, -, hcen𝔭, hloc𝔭⟩ := hrest hFD hsep
  have h𝔭𝔮 : 𝔭 = 𝔮 := by
    ext x; rw [hcen𝔭, hcenV]
  subst h𝔭𝔮
  refine ⟨V, hloc𝔭, hRV, hϖV, ?_⟩
  intro O hAO hcenO

  have hcinv : ∀ c : ↥(chartAlgFin R F f), c ∉ 𝔭 → ((c : F))⁻¹ ∈ O := by
    intro c hc
    have hcu : IsUnit (⟨(c : F), hAO c⟩ : ↥O) := by
      by_contra hu
      exact hc ((hcenO c).2 ((ValuationSubring.coe_mem_nonunits_iff (A := O) (a := ⟨_, hAO c⟩)).2
        ((mem_maximalIdeal _).2 hu)))
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hcu
    have hwval : (w : F) = (c : F)⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)
    rw [← hwval]; exact w.2
  have hVO : V ≤ O := by
    intro y hy
    obtain ⟨b, c, hc, hyc⟩ := (hloc𝔭 y).1 hy
    have hc0 : (c : F) ≠ 0 := fun h0 => hc (by
      have : c = 0 := Subtype.ext h0
      rw [this]; exact 𝔭.zero_mem)
    have : y = (b : F) * ((c : F))⁻¹ := by rw [← hyc, mul_inv_cancel_right₀ hc0]
    rw [this]
    exact O.mul_mem _ _ (hAO b) (hcinv c hc)
  have hOV : O ≤ V := by
    rw [← ValuationSubring.nonunits_le_nonunits]
    intro y hy
    have hyV : y ∈ V := ValuationSubring.nonunits_subset hy
    obtain ⟨b, c, hc, hyc⟩ := (hloc𝔭 y).1 hyV
    have hc0 : (c : F) ≠ 0 := fun h0 => hc (by
      have : c = 0 := Subtype.ext h0
      rw [this]; exact 𝔭.zero_mem)
    by_cases hb : b ∈ 𝔭
    · have hbO : (⟨(b : F), hAO b⟩ : ↥O) ∈ maximalIdeal ↥O :=
        (ValuationSubring.coe_mem_nonunits_iff (A := O) (a := ⟨_, hAO b⟩)).1 ((hcenO b).1 hb)
      have hprod := (maximalIdeal ↥O).mul_mem_right (⟨((c : F))⁻¹, hcinv c hc⟩ : ↥O) hbO
      have hval : (⟨(b : F), hAO b⟩ : ↥O) * ⟨((c : F))⁻¹, hcinv c hc⟩ = ⟨y, hVO hyV⟩ :=
        Subtype.ext (by change (b : F) * ((c : F))⁻¹ = y; rw [← hyc, mul_inv_cancel_right₀ hc0])
      rw [hval] at hprod
      exact (ValuationSubring.coe_mem_nonunits_iff (A := O) (a := ⟨y, hVO hyV⟩)).2 hprod
    ·
      exfalso
      have hb0 : (b : F) ≠ 0 := fun h0 => hb (by
        have : b = 0 := Subtype.ext h0
        rw [this]; exact 𝔭.zero_mem)
      have hy0 : y ≠ 0 := fun h0 => hb0 (by rw [← hyc, h0, zero_mul])
      have hyinv : y⁻¹ ∈ V := (hloc𝔭 _).2 ⟨c, b, hb, by rw [← hyc, ← mul_assoc, inv_mul_cancel₀ hy0, one_mul]⟩
      rw [ValuationSubring.mem_nonunits_iff_or] at hy
      rcases hy with h | h
      · exact hy0 h
      · exact h hyinv
  exact le_antisymm hOV hVO

end CompSupport

open CompSupport in
theorem main
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι]

    (𝔮 : ι → Ideal ↥(chartAlgFin R F f))
    (h𝔮 : ∀ i, 𝔮 i ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes)
    (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal) (h𝔮𝔪 : ∀ i, 𝔮 i ≤ 𝔪 i)
    (honly : ∀ i, ∀ 𝔮' ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes, 𝔮' ≤ 𝔪 i → 𝔮' = 𝔮 i)

    (t : ι → ↥(chartAlgFin R F f)) (ht : ∀ i, t i ∈ 𝔪 i) (ht𝔮 : ∀ i, t i ∉ 𝔮 i)
    (I : ι → Ideal ↥(chartAlgFin R F f)) (htI : ∀ i, t i ∈ I i)
    (hle : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → I i ≤ P → P ≤ 𝔪 i)

    (n : ℕ) (hn : 1 ≤ n) (g : F)
    (h1 : ∀ 𝔭 : Ideal ↥(chartAlgFin R F f), 𝔭.IsPrime → (∀ i, ¬ I i ≤ 𝔭) →
      ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔭 ∧ g * (c : F) = (b : F))
    (h2 : ∀ 𝔭' : Ideal ↥(chartAlgInf R F f), 𝔭'.IsPrime → jInvChartInf R F f ∈ 𝔭' →
      ∃ b c : ↥(chartAlgInf R F f), c ∉ 𝔭' ∧ g * (c : F) = (b : F))
    (h3 : ∀ i, ∃ b c : ↥(chartAlgFin R F f), b ∉ 𝔪 i ∧ c ∉ 𝔪 i ∧ g * (t i : F) ^ n * (c : F) = (b : F)) :
    (Nonempty ι → Transcendental R g) ∧
    ∀ O : ValuationSubring F, (∀ a : R, algebraMap R F a ∈ O) → algebraMap R F ϖ ∈ O.nonunits →
      ((∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O) ↔
        ∃ i, ∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 i ∧ y * (c : F) = (b : F)) := by
  classical

  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hf0 : f ≠ 0 := Fact.out
  haveI hfi : Fact (f⁻¹ ≠ 0) := ⟨inv_ne_zero hf0⟩
  have htf' : Transcendental R f⁻¹ := fun h => htf (IsAlgebraic.inv_iff.mp h)
  have hadj : IntermediateField.adjoin K₀ ({f⁻¹} : Set F) = IntermediateField.adjoin K₀ ({f} : Set F) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self K₀ f)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h := inv_mem (IntermediateField.mem_adjoin_simple_self K₀ f⁻¹)
      rwa [inv_inv] at h
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f⁻¹} : Set F)) F := by rw [hadj]; exact hFD
  have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f⁻¹} : Set F)) F := by rw [hadj]; exact hsep
  obtain ⟨hFT, hFT'⟩ := finiteType_chartAlgFin_and_chartAlgInf R K₀ F f htf hFD hsep
  haveI := hFT
  haveI := hFT'
  have hϖprime : Prime ϖ := by
    have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
    exact hirr.prime
  have hϖ0 : algebraMap R F ϖ ≠ 0 := (map_ne_zero_iff _ hRF).2 hϖprime.ne_zero
  have hXndvd : ¬ (Polynomial.C ϖ ∣ (Polynomial.X : Polynomial R)) := by
    rintro ⟨q, hq⟩
    have := congrArg (fun p : Polynomial R => p.coeff 1) hq
    simp only [Polynomial.coeff_X_one, Polynomial.coeff_C_mul] at this
    have hu : IsUnit ϖ := IsUnit.of_mul_eq_one (q.coeff 1) this.symm
    exact (IsLocalRing.mem_maximalIdeal ϖ).mp (hϖ.symm ▸ Ideal.mem_span_singleton_self ϖ) hu

  have h𝔮p : ∀ i, (𝔮 i).IsPrime := fun i => (h𝔮 i).1.1
  have hϖ𝔮 : ∀ i, algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔮 i := fun i =>
    (h𝔮 i).1.2 (Ideal.subset_span (Set.mem_singleton _))

  have hnotI : ∀ (𝔭 : Ideal ↥(chartAlgFin R F f)), 𝔭.IsPrime → (∀ j, 𝔭 ≤ 𝔪 j → False) → ∀ j, ¬ I j ≤ 𝔭 :=
    fun 𝔭 h𝔭 h j hIj => h j (hle j 𝔭 h𝔭 hIj)
  have hg𝔮 : ∀ i, ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 i ∧ g * (c : F) = (b : F) := by
    intro i
    refine h1 (𝔮 i) (h𝔮p i) (fun j hIj => ht𝔮 j ?_)
    have hij : 𝔮 i = 𝔮 j := honly j (𝔮 i) (h𝔮 i) (hle j (𝔮 i) (h𝔮p i) hIj)
    exact hij ▸ hIj (htI j)

  have hV : ∀ i, ∃ V : ValuationSubring F,
      (∀ y : F, y ∈ V ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 i ∧ y * (c : F) = (b : F)) ∧
      (∀ a : R, algebraMap R F a ∈ V) ∧ algebraMap R F ϖ ∈ V.nonunits ∧
      ∀ O : ValuationSubring F, (∀ x : ↥(chartAlgFin R F f), (x : F) ∈ O) →
        (∀ x : ↥(chartAlgFin R F f), x ∈ 𝔮 i ↔ (x : F) ∈ O.nonunits) → O = V :=
    fun i => CompSupport.exists_valuationSubring_forall_mem_iff_and_eq R F ϖ hϖ K₀ f htf hFD hsep (𝔮 i) (h𝔮 i)

  have hgaussV : ∀ i (O : ValuationSubring F),
      (∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 i ∧ y * (c : F) = (b : F)) →
      ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O := by
    intro i O hO
    haveI := h𝔮p i
    exact forall_aeval_mem_and_inv_mem_of_mul_pow_mul_eq_of_le_of_isMaximal R ϖ hϖ K₀ F f (𝔮 i) (hϖ𝔮 i)
      (𝔪 i) (h𝔪 i) (h𝔮𝔪 i) (t i) (ht i) (ht𝔮 i) n hn g (hg𝔮 i) (h3 i) O hO
  refine ⟨?_, ?_⟩
  ·
    rintro ⟨i⟩
    obtain ⟨V, hVmem, hRV, hϖV, -⟩ := hV i
    have hgauss := hgaussV i V hVmem
    have hgV : g ∈ V := by simpa using (hgauss Polynomial.X hXndvd).1
    have hϖ0 : algebraMap R F ϖ ≠ 0 := (map_ne_zero_iff _ hRF).2 hϖprime.ne_zero
    have hgeo := CompSupport.isUnit_aeval_of_gauss R F ϖ hϖ V hϖV hϖ0 g hgauss
    obtain ⟨-, -, htg, -, -, -, -⟩ :=
      ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
        R ϖ hϖ K₀ F V hRV hϖV g hgV hgeo
    exact htg
  ·
    intro O hRO hϖO
    constructor
    · intro hgauss
      have hgO : g ∈ O := by simpa using (hgauss Polynomial.X hXndvd).1
      by_cases hfO : f ∈ O
      ·
        have hAO := CompSupport.chartAlgFin_le R F f O hRO hfO
        obtain ⟨𝔭, h𝔭p, hϖ𝔭, hcen, -⟩ := CompSupport.exists_centre R F ϖ (chartAlgFin R F f) O hAO hϖO
        haveI := h𝔭p
        rcases mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin R ϖ hϖ K₀ F f htf hFD hsep 𝔭 hϖ𝔭 with hmin | hmax
        ·
          obtain ⟨V, hVmem, -, -, huniq⟩ :=
            CompSupport.exists_valuationSubring_forall_mem_iff_and_eq R F ϖ hϖ K₀ f htf hFD hsep 𝔭 hmin
          have hOV : O = V := huniq O hAO hcen
          by_cases hex : ∃ i, 𝔭 = 𝔮 i
          · obtain ⟨i, hi⟩ := hex
            exact ⟨i, fun y => by rw [hOV, ← hi]; exact hVmem y⟩
          · exfalso
            push Not at hex
            refine not_forall_aeval_mem_and_inv_mem_of_forall_lt_of_forall_jInvChartInf_mem R ϖ hϖ K₀ F f 𝔭 hϖ𝔭 g
              ?_ h2 O (fun y => by rw [hOV]; exact hVmem y) hgauss
            intro 𝔭' h𝔭' hlt
            refine h1 𝔭' h𝔭' (fun j hIj => hex j ?_)
            exact honly j 𝔭 hmin (hlt.le.trans (hle j 𝔭' h𝔭' hIj))
        ·
          exfalso
          by_cases hex : ∃ i, 𝔭 = 𝔪 i
          · obtain ⟨i, hi⟩ := hex
            subst hi
            exact CompSupport.not_mem_of_mul_pow_mul_eq R F (chartAlgFin R F f) O hAO (𝔪 i) hcen (t i) (ht i) n hn g
              (h3 i) hgO
          · push Not at hex
            refine CompSupport.not_gauss_of_isMaximal_centre R F ϖ hϖ hϖ0 (chartAlgFin R F f) O hAO hϖO 𝔭 hmax hcen g
              ?_ hgauss
            refine h1 𝔭 h𝔭p (fun j hIj => hex j ?_)
            exact hmax.eq_of_le (h𝔪 j).ne_top (hle j 𝔭 h𝔭p hIj)
      ·
        exfalso
        have hfinvO : f⁻¹ ∈ O := (O.mem_or_inv_mem f).resolve_left hfO
        have hfinvnu : f⁻¹ ∈ O.nonunits := O.inv_mem_nonunits_iff.mpr (Or.inr hfO)
        have hA'O : ∀ x : ↥(chartAlgInf R F f), (x : F) ∈ O := CompSupport.chartAlgFin_le R F f⁻¹ O hRO hfinvO
        obtain ⟨𝔭, h𝔭p, hϖ𝔭, hcen, -⟩ := CompSupport.exists_centre R F ϖ (chartAlgInf R F f) O hA'O hϖO
        haveI := h𝔭p
        have hjmem : jInvChartInf R F f ∈ 𝔭 := (hcen _).2 (by simpa using hfinvnu)
        have hmax : 𝔭.IsMaximal := by
          rcases mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin R ϖ hϖ K₀ F f⁻¹ htf' hFD' hsep' 𝔭 hϖ𝔭 with hmin | hmax
          · exact absurd hjmem (jInvChartInf_not_mem_of_mem_minimalPrimes_span R K₀ F f htf hFD hsep ϖ hϖprime 𝔭 hmin)
          · exact hmax
        exact CompSupport.not_gauss_of_isMaximal_centre R F ϖ hϖ hϖ0 (chartAlgInf R F f) O hA'O hϖO 𝔭 hmax hcen g
          (h2 𝔭 h𝔭p hjmem) hgauss
    · rintro ⟨i, hi⟩
      exact hgaussV i O hi

end AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι]

    (𝔮 : ι → Ideal ↥(chartAlgFin R F f))
    (h𝔮 : ∀ i, 𝔮 i ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes)
    (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal) (h𝔮𝔪 : ∀ i, 𝔮 i ≤ 𝔪 i)
    (honly : ∀ i, ∀ 𝔮' ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes, 𝔮' ≤ 𝔪 i → 𝔮' = 𝔮 i)

    (t : ι → ↥(chartAlgFin R F f)) (ht : ∀ i, t i ∈ 𝔪 i) (ht𝔮 : ∀ i, t i ∉ 𝔮 i)
    (I : ι → Ideal ↥(chartAlgFin R F f)) (htI : ∀ i, t i ∈ I i)
    (hle : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → I i ≤ P → P ≤ 𝔪 i)

    (n : ℕ) (hn : 1 ≤ n) (g : F)
    (h1 : ∀ 𝔭 : Ideal ↥(chartAlgFin R F f), 𝔭.IsPrime → (∀ i, ¬ I i ≤ 𝔭) →
      ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔭 ∧ g * (c : F) = (b : F))
    (h2 : ∀ 𝔭' : Ideal ↥(chartAlgInf R F f), 𝔭'.IsPrime → jInvChartInf R F f ∈ 𝔭' →
      ∃ b c : ↥(chartAlgInf R F f), c ∉ 𝔭' ∧ g * (c : F) = (b : F))
    (h3 : ∀ i, ∃ b c : ↥(chartAlgFin R F f), b ∉ 𝔪 i ∧ c ∉ 𝔪 i ∧ g * (t i : F) ^ n * (c : F) = (b : F)) :
    (Nonempty ι → Transcendental R g) ∧
    ∀ O : ValuationSubring F, (∀ a : R, algebraMap R F a ∈ O) → algebraMap R F ϖ ∈ O.nonunits →
      ((∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval g P ∈ O ∧ (Polynomial.aeval g P)⁻¹ ∈ O) ↔
        ∃ i, ∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔮 i ∧ y * (c : F) = (b : F)) :=
  AlgebraicCurve.TwoChartIntegralModel.main R ϖ hϖ K₀ F f htf hFD hsep 𝔮 h𝔮 𝔪 h𝔪 h𝔮𝔪 honly t ht ht𝔮 I htI hle n hn g h1 h2 h3

end S_AlgebraicCurve_TwoChartIntegralModel_forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_over_gauss_iff_exists_forall_mem_iff_of_mul_pow_isUnit_of_forall_mem_localization (solution)
