-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.placeMap_unique_of_forall_mapDomain_eq_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d5a6d58c-e2ab-5002-8c3e-ace6c00d0d13

import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_placeMap_unique_of_forall_mapDomain_eq_ord
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open AlgebraicCurve

namespace W5Aux1
namespace PlaceMapU

theorem isEmpty_place_of_finite (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] : IsEmpty (Place K E) := by
  refine ⟨fun v => v.ne_top' (top_le_iff.mp fun y _ => ?_)⟩
  have hy : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hy' : IsIntegral v.toValuationSubring y := hy.tower_top
  obtain ⟨z, hz⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := v.toValuationSubring) (K := E)).mp hy'
  rw [← hz]
  exact z.2

theorem exists_neg_of_mapDomain_neg {α β : Type*} (r : α → β) (D : α →₀ ℤ) (Q : β)
    (h : Finsupp.mapDomain r D Q < 0) : ∃ P, r P = Q ∧ D P < 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hsum : Finsupp.mapDomain r D Q = ∑ P ∈ D.support, (if r P = Q then D P else 0) := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    simp only [Finsupp.sum, Finsupp.single_apply]
  have h0 : 0 ≤ Finsupp.mapDomain r D Q := by
    rw [hsum]
    refine Finset.sum_nonneg fun P _ => ?_
    split_ifs with hP
    · exact hcon P hP
    · exact le_rfl
  exact absurd h (not_lt.mpr h0)

theorem sum_mapDomain_eq {α β : Type*} (r : α → β) (D : α →₀ ℤ) :
    (Finsupp.mapDomain r D).sum (fun _ n => n) = D.sum (fun _ n => n) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem exists_neg_of_sum_eq_zero_of_pos {β : Type*} (G : β →₀ ℤ)
    (hsum : G.sum (fun _ n => n) = 0) {Q₀ : β} (hpos : 0 < G Q₀) : ∃ Q, G Q < 0 := by
  by_contra hcon
  push Not at hcon
  have hsum' : ∑ Q ∈ G.support, G Q = 0 := hsum
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun Q _ => hcon Q)).mp hsum'
  have hQ₀ : Q₀ ∈ G.support := Finsupp.mem_support_iff.mpr hpos.ne'
  exact absurd (hall Q₀ hQ₀) hpos.ne'

section PlaceFacts

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem adicValuation_le_one_of_mem (v : Place K E) {f : E} (hf : f ∈ v.toValuationSubring) :
    v.adicValuation f ≤ 1 := by
  have h := v.adicValuation_coe ⟨f, hf⟩
  rw [show (((⟨f, hf⟩ : v.toValuationSubring) : E)) = f from rfl] at h
  rw [h]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _

theorem ord_nonneg_of_mem (v : Place K E) {f : E} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · have h1 : v.adicValuation f ≤ WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_zero]
      exact adicValuation_le_one_of_mem v hf
    rcases (v.adicValuation_le_exp_iff).mp h1 with h | h
    · exact absurd h hf0
    · simpa using h

theorem mem_of_ord_nonneg (v : Place K E) {f : E} (hf0 : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem ord_pos_of_residue_eq_zero (v : Place K E) {f : E} (hf : f ∈ v.toValuationSubring)
    (hf0 : f ≠ 0) (hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0) : 0 < v.ord f := by
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres
  have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := (IsLocalRing.mem_maximalIdeal _).mp hmax
  have hne1 : v.adicValuation f ≠ 1 := fun h1 =>
    hnu ((v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mp h1)
  have hlt : v.adicValuation f < 1 := lt_of_le_of_ne (adicValuation_le_one_of_mem v hf) hne1
  rw [v.adicValuation_eq_exp_neg_ord hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

theorem degree_eq_sum [IsAlgClosed K] [IsCurveOver K E] (D : Divisor K E) :
    Divisor.degree D = D.sum (fun _ n => n) := by
  have hdeg : ∀ v : Place K E, (v.deg : ℤ) = 1 := fun v => by
    haveI := IsCurveOver.finite_residueField v
    rw [Place.deg_eq_one_of_isAlgClosed_of_finite]
    rfl
  show Finsupp.liftAddHom (fun v => AddMonoidHom.mulRight (v.deg : ℤ)) D = _
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  show D v * (v.deg : ℤ) = D v
  rw [hdeg, mul_one]

theorem exists_residue_eq_algebraMap [IsAlgClosed K] [IsCurveOver K E] (v : Place K E)
    (w : v.ResidueField) : ∃ a : K, algebraMap K v.ResidueField a = w := by
  haveI := IsCurveOver.finite_residueField v
  have h1 : Module.finrank K v.ResidueField = 1 := Place.deg_eq_one_of_isAlgClosed_of_finite v
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp h1 w
  exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one]; exact ha⟩

end PlaceFacts

end W5Aux1.PlaceMapU

open W5Aux1.PlaceMapU in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers)
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hfinF : 0 < Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F)
    (r₁ r₂ : Place L F → Place (IsLocalRing.ResidueField A) Fbar)
    (h₁ : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
      ∀ Q, Finsupp.mapDomain r₁ D Q = Q.ord (R.residue f))
    (h₂ : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
      ∀ Q, Finsupp.mapDomain r₂ D Q = Q.ord (R.residue f)) :
    r₁ = r₂ := by
  classical
  set k := IsLocalRing.ResidueField A with hk
  haveI : IsAlgClosed k := ValuationSubring.isAlgClosed_residueField A

  rcases isEmpty_or_nonempty (Place k Fbar) with hE | ⟨⟨Q₀⟩⟩
  · funext P; exact isEmptyElim (r₁ P)
  funext P₀

  haveI hfdF : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos hfinF
  haveI hfdFb : FiniteDimensional (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin

  have htr : Transcendental L (x : F) := by
    intro halg
    haveI : FiniteDimensional L (IntermediateField.adjoin L ({(x : F)} : Set F)) :=
      IntermediateField.adjoin.finiteDimensional halg.isIntegral
    haveI : FiniteDimensional L F :=
      Module.Finite.trans (IntermediateField.adjoin L ({(x : F)} : Set F)) F
    exact (isEmpty_place_of_finite L F).false P₀
  have hx0 : (x : F) ≠ 0 := fun h0 => htr (h0 ▸ isAlgebraic_zero)

  have hxbar : R.residue x ∉ Set.range (algebraMap k Fbar) := by
    rintro ⟨a, ha⟩
    have hint : IsIntegral k (R.residue x) := ha ▸ isIntegral_algebraMap
    haveI : FiniteDimensional k (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) :=
      IntermediateField.adjoin.finiteDimensional hint
    haveI : FiniteDimensional k Fbar :=
      Module.Finite.trans (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar
    exact (isEmpty_place_of_finite k Fbar).false Q₀
  have hxbar0 : R.residue x ≠ 0 := fun h0 => hxbar ⟨0, by rw [map_zero, h0]⟩

  haveI : Algebra.EssFiniteType L F :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hfdF
  obtain ⟨Kc, g, hRR⟩ := AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch L F

  obtain ⟨Dx, hDx, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (x : F) hx0
  let E : Divisor L F := Finsupp.mapRange (fun n : ℤ => max 0 (-n)) (by simp) Dx
  have hE : ∀ P, E P = max 0 (-P.ord (x : F)) := fun P => by
    show max 0 (-Dx P) = _; rw [hDx]
  have hEnn : ∀ P, 0 ≤ E P := fun P => by rw [hE]; exact le_max_left _ _
  set m : ℤ := E.sum (fun _ n => n) with hm
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun P _ => hEnn P
  let D : Divisor L F := (((g : ℤ) + m) • Finsupp.single P₀ 1) - E
  have hDP : ∀ P, P ≠ P₀ → D P = -E P := fun P hP => by
    show ((((g : ℤ) + m) • Finsupp.single P₀ (1 : ℤ)) - E) P = -E P
    rw [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_eq_of_ne hP, smul_zero, zero_sub]
  have hdegP₀ : (P₀.deg : ℤ) = 1 := by
    haveI := IsCurveOver.finite_residueField P₀
    rw [Place.deg_eq_one_of_isAlgClosed_of_finite]
    rfl
  have hdegD : Divisor.degree D = g := by
    show Divisor.degree ((((g : ℤ) + m) • Finsupp.single P₀ (1 : ℤ)) - E) = g
    rw [map_sub, map_zsmul, Divisor.degree_single, degree_eq_sum E, ← hm, hdegP₀]
    ring

  have hell : 1 ≤ (ell D : ℤ) := by
    have h := hRR D
    have h0 : (0 : ℤ) ≤ ell (Kc - D) := Nat.cast_nonneg _
    rw [hdegD] at h
    linarith
  have hell' : 0 < Module.finrank L (LSpace D) := by exact_mod_cast hell
  haveI := Module.nontrivial_of_finrank_pos hell'
  obtain ⟨⟨h, hhD⟩, hh⟩ := exists_ne (0 : LSpace D)
  have hh0' : (h : F) ≠ 0 := fun h0 => hh (Subtype.ext h0)
  have hordh : ∀ P, P ≠ P₀ → 0 ≤ P.ord (h : F) ∧ 0 ≤ P.ord ((x : F) * h) := fun P hP => by
    have hmem := (mem_riemannRochSpace_iff.mp hhD) P
    rcases hmem with h0 | hle
    · exact absurd h0 hh0'
    · rw [hDP P hP, neg_neg, hE] at hle
      refine ⟨le_trans (le_max_left _ _) hle, ?_⟩
      rw [P.ord_mul hx0 hh0']
      have := le_trans (le_max_right _ _) hle
      linarith

  obtain ⟨c₁, hc₁, hu₁⟩ := R.exists_smul_mem (h : F) hh0'
  obtain ⟨c₂, hc₂, hu₂⟩ := R.exists_smul_mem ((x : F) * h) (mul_ne_zero hx0 hh0')
  have hc₁0 : c₁ ≠ 0 := R.smul_const_ne_zero hc₁ hu₁
  have hc₂0 : c₂ ≠ 0 := R.smul_const_ne_zero hc₂ hu₂
  set u₁ : R.integers := ⟨c₁ • (h : F), hc₁⟩ with hu₁def
  set u₂ : R.integers := ⟨c₂ • ((x : F) * h), hc₂⟩ with hu₂def

  have hord_const : ∀ (P : Place L F) {c : L}, c ≠ 0 → P.ord (algebraMap L F c) = 0 :=
    fun P c hc => ConstantReduction.ord_algebraMap P hc
  have hordu : ∀ P, P ≠ P₀ → 0 ≤ P.ord (u₁ : F) ∧ 0 ≤ P.ord (u₂ : F) := fun P hP => by
    obtain ⟨hh1, hh2⟩ := hordh P hP
    refine ⟨?_, ?_⟩
    · show 0 ≤ P.ord (c₁ • (h : F))
      rw [Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr hc₁0) hh0', hord_const P hc₁0, zero_add]
      exact hh1
    · show 0 ≤ P.ord (c₂ • ((x : F) * h))
      rw [Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr hc₂0) (mul_ne_zero hx0 hh0'),
        hord_const P hc₂0, zero_add]
      exact hh2

  have hnc : R.residue u₁ ∉ Set.range (algebraMap k Fbar) ∨ R.residue u₂ ∉ Set.range (algebraMap k Fbar) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩ := hcon

    have hu₂unit : IsUnit u₂ := R.isUnit_of_residue_ne_zero hu₂
    obtain ⟨w, hw⟩ := hu₂unit.exists_right_inv
    have hwF : (u₂ : F) * (w : F) = 1 := by
      have := congrArg (fun z : R.integers => (z : F)) hw
      simpa using this

    set d : L := c₁ / c₂ with hd
    have hu₂F : (u₂ : F) = algebraMap L F c₂ * ((x : F) * h) := Algebra.smul_def _ _
    have hu₁F : (u₁ : F) = algebraMap L F c₁ * (h : F) := Algebra.smul_def _ _
    have hid' : (x : F) * (u₁ : F) = algebraMap L F d * (u₂ : F) := by
      rw [hu₁F, hu₂F, ← mul_assoc (algebraMap L F d), ← map_mul, hd, div_mul_cancel₀ _ hc₂0]
      ring
    have hdF : algebraMap L F d = (x : F) * (u₁ : F) * (w : F) := by
      rw [hid', mul_assoc, hwF, mul_one]
    have hdO : algebraMap L F d ∈ R.integers := by
      rw [hdF]; exact mul_mem (mul_mem x.2 u₁.2) w.2
    have hdA : d ∈ A := (R.algebraMap_mem_iff d).mp hdO

    have hres_d : R.residue ⟨algebraMap L F d, hdO⟩ = algebraMap k Fbar (IsLocalRing.residue A ⟨d, hdA⟩) :=
      R.residue_algebraMap ⟨d, hdA⟩
    have hid : x * u₁ * w = ⟨algebraMap L F d, hdO⟩ := Subtype.ext (by
      show (x : F) * (u₁ : F) * (w : F) = algebraMap L F d
      rw [hdF])
    have hres := congrArg R.residue hid
    rw [map_mul, map_mul, hres_d, ← ha₁] at hres
    have hresw : R.residue w * algebraMap k Fbar a₂ = 1 := by
      rw [ha₂, mul_comm, ← map_mul, hw, map_one]
    have ha₁0 : algebraMap k Fbar a₁ ≠ 0 := by rw [ha₁]; exact hu₁
    refine hxbar ⟨IsLocalRing.residue A ⟨d, hdA⟩ * a₂ * a₁⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv₀, ← hres,
      show R.residue x * algebraMap k Fbar a₁ * R.residue w * algebraMap k Fbar a₂
          = R.residue x * algebraMap k Fbar a₁ * (R.residue w * algebraMap k Fbar a₂) from by ring,
      hresw, mul_one, mul_inv_cancel_right₀ ha₁0]

  obtain ⟨f, hfnc, hf0, hordf⟩ : ∃ f : R.integers, R.residue f ∉ Set.range (algebraMap k Fbar) ∧
      R.residue f ≠ 0 ∧ ∀ P, P ≠ P₀ → 0 ≤ P.ord (f : F) := by
    rcases hnc with hnc | hnc
    · exact ⟨u₁, hnc, hu₁, fun P hP => (hordu P hP).1⟩
    · exact ⟨u₂, hnc, hu₂, fun P hP => (hordu P hP).2⟩

  have key : ∀ (r : Place L F → Place k Fbar)
      (hr : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f))
      (φ : R.integers), R.residue φ ≠ 0 → (∀ P, P ≠ P₀ → 0 ≤ P.ord (φ : F)) →
      ∀ (Dφ : Divisor L F), (∀ P, Dφ P = P.ord (φ : F)) → ∀ Q, Finsupp.mapDomain r Dφ Q < 0 → r P₀ = Q := by
    intro r hr φ hφ hpole Dφ hDφ Q hneg
    obtain ⟨P, hPQ, hP⟩ := exists_neg_of_mapDomain_neg r Dφ Q hneg
    by_cases hPP : P = P₀
    · rw [← hPP]; exact hPQ
    · rw [hDφ] at hP
      exact absurd (hpole P hPP) (not_le.mpr hP)
  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := L) (f : F)
    (fun h0 => hf0 (by rw [show f = 0 from Subtype.ext h0, map_zero]))
  by_cases hneg : Q₀.ord (R.residue f) < 0
  ·
    have e₁ : r₁ P₀ = Q₀ := key r₁ h₁ f hf0 hordf Df hDf Q₀ (by rw [h₁ f hf0 Df hDf]; exact hneg)
    have e₂ : r₂ P₀ = Q₀ := key r₂ h₂ f hf0 hordf Df hDf Q₀ (by rw [h₂ f hf0 Df hDf]; exact hneg)
    rw [e₁, e₂]
  ·
    push Not at hneg
    have hfbarQ : R.residue f ∈ Q₀.toValuationSubring := mem_of_ord_nonneg Q₀ hf0 hneg
    obtain ⟨a, ha⟩ := exists_residue_eq_algebraMap Q₀
      (IsLocalRing.residue Q₀.toValuationSubring ⟨R.residue f, hfbarQ⟩)
    obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective a
    have hcO : algebraMap L F (c : L) ∈ R.integers := (R.algebraMap_mem_iff (c : L)).mpr c.2
    set g' : R.integers := f - ⟨algebraMap L F (c : L), hcO⟩ with hg'
    have hres_c : R.residue ⟨algebraMap L F (c : L), hcO⟩ = algebraMap k Fbar a := by
      rw [← hc]; exact R.residue_algebraMap c
    have hresg : R.residue g' = R.residue f - algebraMap k Fbar a := by
      rw [hg', map_sub, hres_c]
    have hg0 : R.residue g' ≠ 0 := by
      rw [hresg, sub_ne_zero]
      exact fun heq => hfnc ⟨a, heq.symm⟩
    have hgF : (g' : F) = (f : F) - algebraMap L F (c : L) := rfl

    have hordg : ∀ P, P ≠ P₀ → 0 ≤ P.ord (g' : F) := fun P hP => by
      have hfP : (f : F) ∈ P.toValuationSubring := by
        rcases eq_or_ne (f : F) 0 with h0 | h0
        · rw [h0]; exact zero_mem _
        · exact mem_of_ord_nonneg P h0 (hordf P hP)
      have hcP : algebraMap L F (c : L) ∈ P.toValuationSubring := P.algebraMap_mem' _
      rw [hgF]
      exact ord_nonneg_of_mem P (sub_mem hfP hcP)

    have hconstQ : algebraMap k Fbar a ∈ Q₀.toValuationSubring := Q₀.algebraMap_mem' a
    have hgQmem : R.residue g' ∈ Q₀.toValuationSubring := by
      rw [hresg]; exact sub_mem hfbarQ hconstQ
    have hresQ : IsLocalRing.residue Q₀.toValuationSubring ⟨R.residue g', hgQmem⟩ = 0 := by
      have hsplit : (⟨R.residue g', hgQmem⟩ : Q₀.toValuationSubring)
          = ⟨R.residue f, hfbarQ⟩ - algebraMap k Q₀.toValuationSubring a := by
        apply Subtype.ext
        show R.residue g' = R.residue f - ((algebraMap k Q₀.toValuationSubring a : Q₀.toValuationSubring) : Fbar)
        rw [hresg, Place.coe_algebraMap]
      rw [hsplit, map_sub, ← ha, sub_eq_zero]
      rfl
    have hordQ : 0 < Q₀.ord (R.residue g') := ord_pos_of_residue_eq_zero Q₀ hgQmem hg0 hresQ

    obtain ⟨Dg, hDg, hDg0⟩ := HasPrincipalDivisors.exists_divisor (K := L) (g' : F)
      (fun h0 => hg0 (by rw [show g' = 0 from Subtype.ext h0, map_zero]))
    have hsum : (Finsupp.mapDomain r₁ Dg).sum (fun _ n => n) = 0 := by
      rw [sum_mapDomain_eq, ← degree_eq_sum, hDg0]
    have hpos : 0 < Finsupp.mapDomain r₁ Dg Q₀ := by rw [h₁ g' hg0 Dg hDg]; exact hordQ
    obtain ⟨Q₁, hQ₁⟩ := exists_neg_of_sum_eq_zero_of_pos _ hsum hpos
    have e₁ : r₁ P₀ = Q₁ := key r₁ h₁ g' hg0 hordg Dg hDg Q₁ hQ₁
    have hordQ₁ : Q₁.ord (R.residue g') < 0 := by rw [← h₁ g' hg0 Dg hDg]; exact hQ₁
    have e₂ : r₂ P₀ = Q₁ := key r₂ h₂ g' hg0 hordg Dg hDg Q₁ (by rw [h₂ g' hg0 Dg hDg]; exact hordQ₁)
    rw [e₁, e₂]

#print axioms solution

end S_AlgebraicCurve_RegularProlongation_placeMap_unique_of_forall_mapDomain_eq_ord
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_placeMap_unique_of_forall_mapDomain_eq_ord (solution)
