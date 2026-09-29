-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/aa016374-54c0-5a5c-b5a6-2346a0a86f78

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.AlgebraicCurve IsDedekindDomain"

open scoped IntermediateField.algebraAdjoinAdjoin

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.centerHeightOneSpectrum Place.toValuationSubring_eq_of_forall_mem"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext adicValuation adicValuation_coe_eq_one_iff adicValuation_coe_irreducible ord exists_unit_mul_zpow algebraMap_mem' toValuationSubring mem_of_eval_monic_eq_zero centerHeightOneSpectrum toValuationSubring_eq_of_forall_mem"
namespace MovingLemma
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem adicValuation_eq_valuation {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] (v : Place k F) (w : HeightOneSpectrum R)
    (h : v.toValuationSubring = (w.valuation F).valuationSubring) (f : F) :
    v.adicValuation f = w.valuation F f := by
  classical
  let u := w.valuation F

  have hmem : ∀ g : F, g ∈ v.toValuationSubring ↔ u g ≤ 1 := fun g => by
    rw [h, Valuation.mem_valuationSubring_iff]

  have hunit : ∀ g : v.toValuationSubring, IsUnit g ↔ u (g : F) = 1 := by
    intro g
    constructor
    · intro hg
      obtain ⟨g', hg'⟩ := hg.exists_right_inv
      have h1 : u (g : F) ≤ 1 := (hmem _).mp g.2
      have h2 : u ((g' : v.toValuationSubring) : F) ≤ 1 := (hmem _).mp g'.2
      have hprod : u (g : F) * u ((g' : v.toValuationSubring) : F) = 1 := by
        rw [← map_mul, show (g : F) * (g' : F) = ((g * g' : v.toValuationSubring) : F) from rfl, hg']
        simp
      apply le_antisymm h1
      by_contra hlt
      rw [not_le] at hlt
      have : u (g : F) * u ((g' : v.toValuationSubring) : F) < 1 * 1 :=
        mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hlt h2 zero_le' zero_lt_one |>.trans_eq (by simp) |> fun h => h
      rw [hprod] at this
      simp at this
    · intro hg
      have hg0 : (g : F) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hg
        exact zero_ne_one hg
      have hinv : (g : F)⁻¹ ∈ v.toValuationSubring := by
        rw [hmem, map_inv₀, hg, inv_one]
      refine ⟨⟨g, ⟨(g : F)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
      · exact Subtype.ext (mul_inv_cancel₀ hg0)
      · exact Subtype.ext (inv_mul_cancel₀ hg0)

  obtain ⟨ϖ, hϖ⟩ := w.valuation_exists_uniformizer F
  have hϖmem : ϖ ∈ v.toValuationSubring := by
    rw [hmem]
    show w.valuation F ϖ ≤ 1
    rw [hϖ]
    exact le_of_lt (WithZero.exp_lt_exp.mpr (by norm_num))
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.coe_ne_zero hϖ.symm
  set ϖ' : v.toValuationSubring := ⟨ϖ, hϖmem⟩ with hϖ'
  have hϖ'0 : ϖ' ≠ 0 := by
    intro h0
    exact hϖ0 (congrArg Subtype.val h0)
  have hmax : IsLocalRing.maximalIdeal v.toValuationSubring = Ideal.span {ϖ'} := by
    apply le_antisymm
    · intro g hg
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit] at hg
      rcases eq_or_ne g 0 with rfl | hg0
      · exact Ideal.zero_mem _
      have hgF0 : (g : F) ≠ 0 := fun h0 => hg0 (Subtype.ext h0)
      have hle1 : u (g : F) ≤ 1 := (hmem _).mp g.2
      have hlt : u (g : F) < 1 := lt_of_le_of_ne hle1 hg

      have hle : u (g : F) ≤ u ϖ := by
        rw [hϖ]
        have hne : u (g : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr hgF0
        rw [← WithZero.exp_log hne] at hlt ⊢
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
        rw [WithZero.exp_le_exp]
        omega
      have hquot : (g : F) * ϖ⁻¹ ∈ v.toValuationSubring := by
        rw [hmem, map_mul, map_inv₀]
        have huϖ : u ϖ ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0
        calc u (g : F) * (u ϖ)⁻¹ ≤ u ϖ * (u ϖ)⁻¹ := by gcongr
          _ = 1 := mul_inv_cancel₀ huϖ
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨(g : F) * ϖ⁻¹, hquot⟩, Subtype.ext ?_⟩
      show (g : F) * ϖ⁻¹ * ϖ = g
      rw [inv_mul_cancel_right₀ hϖ0]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff, hunit, hϖ]
      intro h1
      have : (-1 : ℤ) = 0 := by
        have := congrArg WithZero.log h1
        rwa [WithZero.log_exp, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 from WithZero.exp_zero.symm,
          WithZero.log_exp] at this
      omega
  have hirr : Irreducible ϖ' :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ' hϖ'0 hmax

  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨e, he⟩ := v.exists_unit_mul_zpow hf0 hirr
  have hue : u ((e : v.toValuationSubring) : F) = 1 := (hunit _).mp e.isUnit
  have hve : v.adicValuation ((e : v.toValuationSubring) : F) = 1 :=
    (v.adicValuation_coe_eq_one_iff _).mpr e.isUnit
  have hvϖ : v.adicValuation ϖ = WithZero.exp (-1 : ℤ) := v.adicValuation_coe_irreducible hirr
  rw [he, map_mul, map_mul, map_zpow₀, map_zpow₀, hue, hve]
  show 1 * v.adicValuation ϖ ^ v.ord f = 1 * u ϖ ^ v.ord f
  rw [hvϖ, hϖ]

scoped instance instIsPrincipalIdealRingAdjoinSingleton (x : F) :
    IsPrincipalIdealRing (Algebra.adjoin k ({x} : Set F)) := by
  have hmem : ∀ p : Polynomial k, Polynomial.aeval x p ∈ Algebra.adjoin k ({x} : Set F) := by
    intro p
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  refine IsPrincipalIdealRing.of_surjective
    ((Polynomial.aeval x).codRestrict (Algebra.adjoin k ({x} : Set F)) hmem) ?_
  rintro ⟨a, ha⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial k, Polynomial.aeval x p = a := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    exact (AlgHom.mem_range _).mp ha
  exact ⟨p, Subtype.ext hp⟩

variable (k) in

abbrev holRing (x : F) : Subalgebra (Algebra.adjoin k ({x} : Set F)) F :=
  integralClosure (Algebra.adjoin k ({x} : Set F)) F

section Dedekind

variable (x : F) [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F]
  [Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F]

scoped instance instIsDedekindDomainHolRing : IsDedekindDomain (holRing k x) :=
  integralClosure.isDedekindDomain (Algebra.adjoin k ({x} : Set F))
    (IntermediateField.adjoin k ({x} : Set F)) F

scoped instance instIsFractionRingHolRing : IsFractionRing (holRing k x) F :=
  integralClosure.isFractionRing_of_finite_extension
    (IntermediateField.adjoin k ({x} : Set F)) F

end Dedekind

theorem forall_mem_of_mem (x : F) (w : Place k F) (hx : x ∈ w.toValuationSubring)
    (a : holRing k x) : algebraMap (holRing k x) F a ∈ w.toValuationSubring := by
  have hadj : ∀ y : F, y ∈ Algebra.adjoin k ({x} : Set F) → y ∈ w.toValuationSubring := by
    intro y hy
    refine Algebra.adjoin_induction (fun z hz => ?_) (fun c => w.algebraMap_mem' c)
      (fun _ _ _ _ h1 h2 => add_mem h1 h2) (fun _ _ _ _ h1 h2 => mul_mem h1 h2) hy
    rw [Set.mem_singleton_iff.mp hz]
    exact hx
  obtain ⟨P, hPmonic, hPeval⟩ : IsIntegral (Algebra.adjoin k ({x} : Set F)) (a : F) := a.2
  refine w.mem_of_eval_monic_eq_zero (P := P.map (algebraMap _ F)) (hPmonic.map _)
    (fun i => ?_) ?_
  · rw [Polynomial.coeff_map]
    exact hadj _ (P.coeff i).2
  · rw [Polynomial.eval_map]
    exact hPeval

theorem exists_isIntegral_and_ord_eq_one_and_forall_ord_eq_zero
    (x : F) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F]
    (S : Finset (Place k F)) (P : Place k F) (hP : P ∈ S)
    (hS : ∀ Q ∈ S, x ∈ Q.toValuationSubring) :
    ∃ y : F, IsIntegral (Algebra.adjoin k ({x} : Set F)) y ∧ P.ord y = 1 ∧
      ∀ Q ∈ S, Q ≠ P → Q.ord y = 0 := by
  classical

  set R := holRing k x with hR
  have hw : ∀ Q ∈ S, ∀ r : R, algebraMap R F r ∈ Q.toValuationSubring :=
    fun Q hQ r => forall_mem_of_mem x Q (hS Q hQ) r
  let ctr : ∀ Q ∈ S, HeightOneSpectrum R := fun Q hQ => Place.centerHeightOneSpectrum R Q (hw Q hQ)
  have hval : ∀ Q (hQ : Q ∈ S) (f : F), Q.adicValuation f = (ctr Q hQ).valuation F f := by
    intro Q hQ f
    apply adicValuation_eq_valuation
    rw [Place.toValuationSubring_eq_of_forall_mem Q (hw Q hQ),
      HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]

  let I : Place k F → Ideal R := fun Q => if hQ : Q ∈ S then (ctr Q hQ).asIdeal else ⊥
  have hI : ∀ Q (hQ : Q ∈ S), I Q = (ctr Q hQ).asIdeal := fun Q hQ => dif_pos hQ
  let e : Place k F → ℕ := fun Q => if Q = P then 2 else 1
  obtain ⟨π, hπ⟩ := (ctr P hP).intValuation_exists_uniformizer
  let t : ↥S → R := fun Q => if (Q : Place k F) = P then π else 1
  have hprime : ∀ Q ∈ S, Prime (I Q) := by
    intro Q hQ
    rw [hI Q hQ]
    exact (ctr Q hQ).prime
  have hcop : ∀ Q ∈ S, ∀ Q' ∈ S, Q ≠ Q' → I Q ≠ I Q' := by
    intro Q hQ Q' hQ' hne heq
    apply hne
    rw [hI Q hQ, hI Q' hQ'] at heq
    have hc : ctr Q hQ = ctr Q' hQ' := HeightOneSpectrum.ext heq
    apply Place.ext
    rw [Place.toValuationSubring_eq_of_forall_mem Q (hw Q hQ),
      Place.toValuationSubring_eq_of_forall_mem Q' (hw Q' hQ')]
    exact congrArg (HeightOneSpectrum.valuationSubringAtPrime F) hc
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal I e hprime hcop t
  refine ⟨algebraMap R F y, ?_, ?_, ?_⟩
  ·
    exact y.2
  ·
    have hyP := hy P hP
    simp only [t, e, if_pos rfl, I, dif_pos hP] at hyP

    have h2 : (ctr P hP).intValuation (y - π) ≤ WithZero.exp (-(2 : ℕ) : ℤ) :=
      ((ctr P hP).intValuation_le_pow_iff_mem _ 2).mpr hyP
    have hvy : (ctr P hP).intValuation y = WithZero.exp (-1 : ℤ) := by
      have hsum : y = π + (y - π) := by ring
      rw [hsum]
      rw [Valuation.map_add_eq_of_lt_left]
      · exact hπ
      · rw [hπ]
        refine lt_of_le_of_lt h2 ?_
        exact WithZero.exp_lt_exp.mpr (by norm_num)
    show -(WithZero.log (P.adicValuation (algebraMap R F y))) = 1
    rw [hval P hP, HeightOneSpectrum.valuation_of_algebraMap, hvy, WithZero.log_exp]
    norm_num
  ·
    intro Q hQ hQP
    have hyQ := hy Q hQ
    simp only [t, e, if_neg hQP, I, dif_pos hQ, pow_one] at hyQ
    have h1 : (ctr Q hQ).intValuation (y - 1) < 1 :=
      ((ctr Q hQ).intValuation_lt_one_iff_mem _).mpr hyQ
    have hvy : (ctr Q hQ).intValuation y = 1 := by
      have hsum : y = 1 + (y - 1) := by ring
      rw [hsum, Valuation.map_add_eq_of_lt_left]
      · exact map_one _
      · rwa [map_one]
    show -(WithZero.log (Q.adicValuation (algebraMap R F y))) = 0
    rw [hval Q hQ, HeightOneSpectrum.valuation_of_algebraMap, hvy]
    simp

end AlgebraicCurve.Place.MovingLemma
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.AlgebraicCurve.Place.MovingLemma"
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero.AlgebraicCurve.Place.MovingLemma"

theorem solution
    {k F : Type*} [Field k] [Field F] [Algebra k F] (x : F) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F]
    (S : Finset (Place k F)) (P : Place k F) (hP : P ∈ S)
    (hS : ∀ Q ∈ S, x ∈ Q.toValuationSubring) :
    ∃ y : F, IsIntegral (Algebra.adjoin k ({x} : Set F)) y ∧ P.ord y = 1 ∧
      ∀ Q ∈ S, Q ≠ P → Q.ord y = 0 :=
  AlgebraicCurve.Place.MovingLemma.exists_isIntegral_and_ord_eq_one_and_forall_ord_eq_zero
    x hx S P hP hS

end S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero (solution)
