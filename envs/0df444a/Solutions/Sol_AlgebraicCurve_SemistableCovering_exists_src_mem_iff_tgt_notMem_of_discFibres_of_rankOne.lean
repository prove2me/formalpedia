-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d742e7ac-ea1d-56d3-a670-fcb8976f7aed

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ConnSol

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_const_smul (v : Place K F) {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) :
    v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero (algebraMap K F)).mpr hc) hf,
    AlgebraicCurve.Place.ord_algebraMap, zero_add]

theorem degree_eq_finsuppDegree (D : Divisor K F) (h : ∀ P ∈ D.support, Place.IsRational P) :
    Divisor.degree D = Finsupp.degree D := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.degree_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  have h1 : P.deg = 1 := (AlgebraicCurve.Place.isRational_iff_deg_eq_one P).mp (h P hP)
  simp [h1]

theorem degree_filter (D : Divisor K F) (p : Place K F → Prop) [DecidablePred p] :
    Finsupp.degree (D.filter p) = ∑ P ∈ D.support.filter p, D P := by
  rw [Finsupp.degree_apply, Finsupp.support_filter]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hP).2]

theorem sum_eq_degree (D : Divisor K F) : (D.sum fun _ n => n) = Finsupp.degree D := by
  rw [Finsupp.degree_apply, Finsupp.sum]

end PlaceFacts

section Infinite

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

theorem infinite_place : Infinite (Place K F) := by
  obtain ⟨t, ht, hfin, -⟩ := (IsCurveOver.exists_separating_transcendental (K := K) (F := F))
  haveI := hfin

  have hpole : ∀ {f : F}, Transcendental K f → ∃ v : Place K F, v.ord f < 0 := by
    intro f hf
    haveI := AlgebraicCurve.finiteDimensional_adjoin_of_transcendental t hf
    classical
    have hf0 : f ≠ 0 := by rintro rfl; exact hf isAlgebraic_zero
    obtain ⟨Df, hDf, -⟩ := (IsCurveOver.hasPrincipalDivisors (K := K) (F := F)).exists_divisor f hf0
    let D : Divisor K F := Finsupp.onFinset Df.support (fun v => max 0 (-v.ord f)) (by
        intro v hv
        rw [Finsupp.mem_support_iff, hDf v]
        intro h0; apply hv; simp [h0])
    have hD : ∀ v, D v = max 0 (-v.ord f) := fun v => by simp [D, Finsupp.onFinset_apply]
    have hdeg := AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental f hf D hD
    have hpos : 0 < Module.finrank (IntermediateField.adjoin K ({f} : Set F)) F := Module.finrank_pos
    have hne : D ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hdeg
      omega
    obtain ⟨v, hv⟩ := Finsupp.ne_iff.mp hne
    refine ⟨v, ?_⟩
    rw [hD v] at hv
    simp only [Finsupp.coe_zero, Pi.zero_apply, ne_eq] at hv
    by_contra hge
    apply hv
    rw [max_eq_left]
    omega
  have hz : ∀ a : K, ∃ v : Place K F, 0 < v.ord (t - algebraMap K F a) := by
    intro a
    have hta : Transcendental K (t - algebraMap K F a)⁻¹ := by
      intro halg
      apply ht
      have h1 : IsAlgebraic K (t - algebraMap K F a) := by simpa using halg.inv
      simpa using h1.add (isAlgebraic_algebraMap a)
    obtain ⟨v, hv⟩ := hpole hta
    refine ⟨v, ?_⟩
    rw [Place.ord_inv] at hv
    omega
  choose z hz using hz
  refine Infinite.of_injective z ?_
  intro a b hab
  by_contra hne
  have ha := hz a
  have hb := hz b
  rw [← hab] at hb
  have hta0 : t - algebraMap K F a ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at ha; exact lt_irrefl _ ha
  have htb0 : t - algebraMap K F b ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hb; exact lt_irrefl _ hb
  have hlt : ∀ {f : F}, f ≠ 0 → 0 < (z a).ord f → (z a).adicValuation f < 1 := by
    intro f hf0 h
    rw [(z a).adicValuation_eq_exp_neg_ord hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have h1 := hlt hta0 ha
  have h2 := hlt htb0 hb
  have hab0 : (b - a : K) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h3 : (z a).adicValuation (algebraMap K F (b - a)) = 1 := by
    rw [(z a).adicValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hab0), Place.ord_algebraMap, neg_zero,
      WithZero.exp_zero]
  have hid : algebraMap K F (b - a) = (t - algebraMap K F a) - (t - algebraMap K F b) := by
    rw [map_sub]; ring
  rw [hid] at h3
  have h4 := Valuation.map_sub (z a).adicValuation (t - algebraMap K F a) (t - algebraMap K F b)
  rw [h3] at h4
  rcases le_max_iff.mp h4 with h | h
  · exact absurd h1 (not_lt.mpr h)
  · exact absurd h2 (not_lt.mpr h)

end Infinite

section DivisorFacts

theorem mapDomain_apply_eq_zero_of_forall_ne {α β : Type*} (φ : α → β) (D : α →₀ ℤ) (b : β)
    (h : ∀ a ∈ D.support, φ a ≠ b) : Finsupp.mapDomain φ D b = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  exact Finset.sum_eq_zero fun a ha => by
    show (Finsupp.single (φ a) (D a)) b = 0
    rw [Finsupp.single_apply, if_neg (h a ha)]

end DivisorFacts

section ChartFacts

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem residue_ne_zero_imp_ne_zero (C : ComponentChart A F Fbar) {c : L} {f : F}
    (hc : c • f ∈ C.integers) (hc0 : C.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hc0
  have h0 : (⟨(0 : L) • f, hc⟩ : C.integers) = 0 := Subtype.ext (zero_smul L f)
  rw [h0, map_zero]

@[reducible] def toRP (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

theorem isAttached_transport (An' : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar)
    (hatt : An'.IsAttached C x) {y : F} (hy : An'.param = y) {S : Set (Place L F)}
    (hS : An'.dom = S) :
    ∃ hz : y ∈ C.integers, x.ord (C.residue ⟨y, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S, P.ord f = 0) →
        ∀ P ∈ S, ∃ h : P.evalAt f * (P.evalAt y) ^ (-(x.ord (C.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by
  subst hy; subst hS
  exact hatt.2

theorem sum_nodes_ord_residue_eq_neg_degree [HasPrincipalDivisors (ResidueField A) Fbar]
    (hratBar : ∀ Q : Place (ResidueField A) Fbar, Q.IsRational)
    (C : ComponentChart A F Fbar) (f : F) (hf0 : f ≠ 0)
    (c : L) (hc : c • f ∈ C.integers) (hc0 : C.residue ⟨c • f, hc⟩ ≠ 0)
    (Ei : Divisor L F) (hEi : ∀ P ∈ C.dom, Ei P = P.ord f) (hEi' : ∀ P, P ∉ C.dom → Ei P = 0) :
    ∑ x ∈ C.nodes, x.ord (C.residue ⟨c • f, hc⟩) = -Finsupp.degree Ei := by
  classical
  set fbar := C.residue ⟨c • f, hc⟩ with hfbar
  have hcne : c ≠ 0 := residue_ne_zero_imp_ne_zero C hc hc0
  obtain ⟨Dbar, hDbar, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A) fbar hc0
  have hM : ∀ Q, Q ∉ C.nodes → Finsupp.mapDomain C.placeMap Ei Q = Q.ord fbar :=
    C.mapDomain_placeMap ⟨c • f, hc⟩ hc0 Ei
      (fun P hP => by rw [hEi P hP]; exact (ord_const_smul P hcne hf0).symm) hEi'
  have hM0 : ∀ Q ∈ C.nodes, Finsupp.mapDomain C.placeMap Ei Q = 0 := by
    intro Q hQ
    refine mapDomain_apply_eq_zero_of_forall_ne _ _ _ fun P hP => ?_
    have hPdom : P ∈ C.dom := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hP) (hEi' P h)
    intro h
    exact C.placeMap_not_mem_nodes P hPdom (h ▸ hQ)
  have hDbar_eq : Dbar = Finsupp.mapDomain C.placeMap Ei +
      ∑ x ∈ C.nodes, Finsupp.single x (x.ord fbar) := by
    ext Q
    rw [Finsupp.add_apply, Finsupp.finsetSum_apply, hDbar Q]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    by_cases hQ : Q ∈ C.nodes
    · rw [if_pos hQ, hM0 Q hQ, zero_add]
    · rw [if_neg hQ, hM Q hQ, add_zero]
  have hdeg' : Finsupp.degree Dbar = 0 := by
    rw [← degree_eq_finsuppDegree Dbar (fun Q _ => hratBar Q)]
    exact hdeg
  rw [hDbar_eq, map_add, Finsupp.degree_mapDomain, map_sum] at hdeg'
  simp only [Finsupp.degree_single] at hdeg'
  linarith

end ChartFacts

section TwoRadii

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem exists_fourth_root [IsAlgClosed L] (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : (π : L) ≠ 0) :
    ∃ s : A, s ∈ maximalIdeal A ∧ (s : L) ≠ 0 ∧ s ^ 4 = π := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (π : L) (by norm_num : 0 < 4)
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hπ0
    rw [← ht]; simp
  have htA : t ∈ A := by
    rcases A.mem_or_inv_mem t with h | h
    · exact h
    · exfalso
      have hinv : (π : L)⁻¹ ∈ A := by
        rw [← ht, ← inv_pow]
        exact pow_mem h 4
      have hunit : IsUnit π := by
        refine ⟨⟨π, ⟨(π : L)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
        · exact Subtype.ext (mul_inv_cancel₀ hπ0)
        · exact Subtype.ext (inv_mul_cancel₀ hπ0)
      exact (IsLocalRing.mem_maximalIdeal _).mp hπ hunit
  refine ⟨⟨t, htA⟩, ?_, ht0, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hπ
    have : π = (⟨t, htA⟩ : A) ^ 4 := Subtype.ext (by push_cast; exact ht.symm)
    rw [this]
    exact hu.pow 4
  · exact Subtype.ext (by push_cast; exact ht)

theorem exists_two_radii [IsAlgClosed L] (An : Annulus A F) (hmod0 : ((An.modulus : A) : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param) := by
  obtain ⟨s, hs, hs0, hs4⟩ := exists_fourth_root An.modulus An.modulus_mem hmod0
  have hadm : ∀ (j : ℕ), 0 < j → j < 4 →
      ∃! P : Place L F, P ∈ An.dom ∧ P.evalAt An.param = ((s ^ j : A) : L) := by
    intro j hj hj4
    apply An.existsUnique_evalAt_eq
    · exact Ideal.pow_mem_of_mem _ hs j hj
    · push_cast; exact pow_ne_zero _ hs0
    · refine ⟨s ^ (4 - j), Ideal.pow_mem_of_mem _ hs _ (by omega), ?_⟩
      rw [← hs4]
      push_cast
      rw [← pow_add, Nat.add_sub_cancel' hj4.le]
  obtain ⟨Q₁, ⟨hQ₁, hQ₁v⟩, -⟩ := hadm 1 one_pos (by norm_num)
  obtain ⟨Q₂, ⟨hQ₂, hQ₂v⟩, -⟩ := hadm 2 (by norm_num) (by norm_num)
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁v, hQ₂v]
  push_cast
  rw [pow_one, Valuation.map_pow]
  intro heq
  have hvs0 : A.valuation (s : L) ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact hs0
  have hone : A.valuation (s : L) = 1 := by
    have : A.valuation (s : L) * 1 = A.valuation (s : L) * A.valuation (s : L) := by
      rw [mul_one, ← sq]; exact heq
    exact (mul_left_cancel₀ hvs0 this).symm
  rw [← ValuationSubring.valuation_eq_one_iff] at hone
  exact (IsLocalRing.mem_maximalIdeal _).mp hs hone

end TwoRadii

section Reindex

theorem sum_nodes_eq_sum_ends {n m : ℕ} {ι : Fin n → Type*} (nodes : ∀ j, Finset (ι j))
    (src tgt : Fin m → Fin n) (xs : ∀ e, ι (src e)) (xt : ∀ e, ι (tgt e))
    (hxs : ∀ e, xs e ∈ nodes (src e)) (hxt : ∀ e, xt e ∈ nodes (tgt e))
    (hex : ∀ i, ∀ x ∈ nodes i, ∃ e,
      (⟨src e, xs e⟩ : Σ j, ι j) = ⟨i, x⟩ ∨ (⟨tgt e, xt e⟩ : Σ j, ι j) = ⟨i, x⟩)
    (huniq : ∀ i, ∀ x ∈ nodes i, ∀ E E' : Fin m ⊕ Fin m,
      Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, ι j)) (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
      Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, ι j)) (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ →
        E = E')
    (G : (Σ j, ι j) → ℤ) (i : Fin n) :
    ∑ x ∈ nodes i, G ⟨i, x⟩ =
      (∑ e ∈ Finset.univ.filter (fun e => src e = i), G ⟨src e, xs e⟩) +
        ∑ e ∈ Finset.univ.filter (fun e => tgt e = i), G ⟨tgt e, xt e⟩ := by
  classical
  set φ : Fin m ⊕ Fin m → Σ j, ι j :=
    Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, ι j)) (fun e => ⟨tgt e, xt e⟩) with hφ
  set N : Finset (Σ j, ι j) := Finset.univ.sigma nodes with hN
  set Gi : (Σ j, ι j) → ℤ := fun σ => if σ.1 = i then G σ else 0 with hGi
  have hmaps : ∀ E ∈ (Finset.univ : Finset (Fin m ⊕ Fin m)), φ E ∈ N := by
    rintro (e | e) -
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hxs e⟩
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hxt e⟩
  have hinj : Set.InjOn φ ↑(Finset.univ : Finset (Fin m ⊕ Fin m)) := by
    intro E hE E' _ h
    have hmem : (φ E).2 ∈ nodes (φ E).1 := (Finset.mem_sigma.mp (hmaps E hE)).2
    exact huniq (φ E).1 (φ E).2 hmem E E' rfl (by rw [← h])
  have hsurj : Set.SurjOn φ ↑(Finset.univ : Finset (Fin m ⊕ Fin m)) ↑N := by
    rintro ⟨j, x⟩ hσ
    have hx : x ∈ nodes j := (Finset.mem_sigma.mp (Finset.mem_coe.mp hσ)).2
    obtain ⟨e, h | h⟩ := hex j x hx
    · exact ⟨Sum.inl e, by simp, h⟩
    · exact ⟨Sum.inr e, by simp, h⟩
  have h1 : ∑ E, Gi (φ E) = ∑ σ ∈ N, Gi σ :=
    Finset.sum_nbij φ hmaps hinj hsurj (fun _ _ => rfl)
  have h2 : ∑ σ ∈ N, Gi σ = ∑ x ∈ nodes i, G ⟨i, x⟩ := by
    rw [hN, Finset.sum_sigma]
    rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)]
    · exact Finset.sum_congr rfl fun x _ => by simp [Gi]
    · exact Finset.sum_eq_zero fun x _ => by simp [Gi, hji]
  have h3 : ∑ E, Gi (φ E) =
      (∑ e ∈ Finset.univ.filter (fun e => src e = i), G ⟨src e, xs e⟩) +
        ∑ e ∈ Finset.univ.filter (fun e => tgt e = i), G ⟨tgt e, xt e⟩ := by
    rw [Fintype.sum_sum_type, Finset.sum_filter, Finset.sum_filter]
    rfl
  rw [← h2, ← h1, h3]

end Reindex

section Mass

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fs : Type*} [Field Fs] [Algebra (ResidueField A) Fs]
variable {Ft : Type*} [Field Ft] [Algebra (ResidueField A) Ft]

theorem annulus_mass [IsAlgClosed L]
    (An An' : Annulus A F) (Cs : ComponentChart A F Fs) (Ct : ComponentChart A F Ft)
    (xs : Place (ResidueField A) Fs) (xt : Place (ResidueField A) Ft)
    (hdom : An'.dom = An.dom) (hmod0 : ((An.modulus : A) : L) ≠ 0)
    (hzz : An'.param * An.param = algebraMap L F (An.modulus : L))
    (hs : An.IsAttached Cs xs) (ht : An'.IsAttached Ct xt)
    (h : F) (hh0 : h ≠ 0)
    (cs : L) (hcs : cs • h ∈ Cs.integers) (hcs0 : Cs.residue ⟨cs • h, hcs⟩ ≠ 0)
    (ct : L) (hct : ct • h ∈ Ct.integers) (hct0 : Ct.residue ⟨ct • h, hct⟩ ≠ 0)
    (E : Divisor L F) (hEsupp : ∀ P ∈ E.support, P ∈ An.dom) (hE : ∀ P ∈ An.dom, E P = P.ord h) :
    (E.sum fun _ n => n) = xs.ord (Cs.residue ⟨cs • h, hcs⟩) + xt.ord (Ct.residue ⟨ct • h, hct⟩) := by
  classical
  have hz0 : An.param ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hzz
    exact hmod0 ((map_eq_zero _).mp hzz.symm)
  have hkey : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ := by
    rw [← hzz, mul_inv_cancel_right₀ hz0]
  obtain ⟨hza, hxa1, hslope_a⟩ := hs.2
  obtain ⟨hzb, hxb1, hslope_b⟩ := isAttached_transport An' Ct xt ht hkey hdom
  have hwide := exists_two_radii An hmod0
  have hcsne : cs ≠ 0 := residue_ne_zero_imp_ne_zero Cs hcs hcs0
  have hctne : ct ≠ 0 := residue_ne_zero_imp_ne_zero Ct hct hct0
  set f : F := cs • h with hf
  have hf0 : f ≠ 0 := smul_ne_zero hcsne hh0
  set c' : L := cs / ct with hc'def
  have hc'0 : c' ≠ 0 := div_ne_zero hcsne hctne
  have heq : (algebraMap L F c')⁻¹ * f = ct • h := by
    rw [hf, hc'def, Algebra.smul_def, Algebra.smul_def, map_div₀, inv_div, ← mul_assoc,
      div_mul_cancel₀ _ ((map_ne_zero _).mpr hcsne)]
  have hhb : (algebraMap L F c')⁻¹ * f ∈ Ct.integers := by rw [heq]; exact hct
  have hsub : (⟨(algebraMap L F c')⁻¹ * f, hhb⟩ : Ct.integers) = ⟨ct • h, hct⟩ := Subtype.ext heq
  have hresb : Ct.residue ⟨(algebraMap L F c')⁻¹ * f, hhb⟩ ≠ 0 := by rw [hsub]; exact hct0
  have hE' : ∀ P ∈ An.dom, E P = P.ord f := fun P hP => by
    rw [hE P hP, hf, ord_const_smul P hcsne hh0]
  obtain ⟨hmass, -⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 (toRP Cs) xs hza hxa1 hslope_a (toRP Ct) xt hzb hxb1 hslope_b hwide
      f hf0 hcs hcs0 c' hc'0 hhb hresb E hEsupp hE'
  rw [hmass]
  show xs.ord (Cs.residue ⟨f, hcs⟩) + xt.ord (Ct.residue ⟨_, hhb⟩) = _
  rw [hsub]

end Mass

end ConnSol

open ConnSol in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    :
    ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S) := by
  intro S hS hSc
  classical
  by_contra hno
  have hcl : ∀ e, src e ∈ S ↔ tgt e ∈ S := by
    intro e
    by_contra h'
    exact hno ⟨e, by tauto⟩
  obtain ⟨i₀, hi₀⟩ := hS
  obtain ⟨j, hj'⟩ := hSc
  have hj : j ∉ S := Finset.mem_compl.mp hj'
  haveI hκ : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hπL : ((π : A) : L) ≠ 0 := fun h => hπ0 (ZeroMemClass.coe_eq_zero.mp h)

  have hdom : ∀ i, ∃ P P' : Place L F, P ∈ (C i).dom ∧ P' ∈ (C i).dom ∧ P ≠ P' := by
    intro i
    haveI := infinite_place (K := ResidueField A) (F := Fbar i)
    obtain ⟨Q, hQ⟩ := Infinite.exists_notMem_finset (C i).nodes
    obtain ⟨T, hT, -, -, -, huniq⟩ := hdisc i Q hQ
    obtain ⟨P, ⟨hP, -, hPT⟩, -⟩ := huniq 0 (Ideal.zero_mem _)
    obtain ⟨P', ⟨hP', -, hP'T⟩, -⟩ := huniq π hπ
    refine ⟨P, P', hP, hP', fun hPP' => hπ0 ?_⟩
    apply Subtype.ext
    rw [hPP'] at hPT
    have : ((π : A) : L) = ((0 : A) : L) := by rw [← hP'T, ← hPT]
    exact_mod_cast this
  obtain ⟨P₀, P₂, hP₀, hP₂, hP₀₂⟩ := hdom i₀
  obtain ⟨P₁, -, hP₁, -, -⟩ := hdom j
  have huniq : ∀ {P : Place L F} {i i' : Fin n}, P ∈ (C i).dom → P ∈ (C i').dom → i = i' := by
    intro P i i' h1 h2
    rcases hcover P with ⟨l, -, hl, -⟩ | ⟨e, -, -, hno'⟩
    · exact (hl i h1).trans (hl i' h2).symm
    · exact absurd h1 (hno' i)
  have hji₀ : j ≠ i₀ := fun h => hj (h ▸ hi₀)
  have hP₁₀ : P₁ ≠ P₀ := fun h => hji₀ (huniq hP₁ (h ▸ hP₀))
  have hP₁₂ : P₁ ≠ P₂ := fun h => hji₀ (huniq hP₁ (h ▸ hP₂))

  obtain ⟨g, hgRR, hgP₁, -⟩ :=
    AlgebraicCurve.exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero L F P₀ P₁ P₂ hP₁₀
      hP₀₂.symm hP₁₂
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [Place.ord_zero] at hgP₁; exact lt_irrefl _ hgP₁
  have hgreg : ∀ P : Place L F, P ≠ P₀ → 0 ≤ P.ord g := by
    intro P hP
    rcases (mem_riemannRochSpace_iff.mp hgRR) P with h | h
    · exact absurd h hg0
    · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg hP.symm, smul_zero, neg_zero] at h
      exact h
  obtain ⟨Dg, hDg, hdegDg⟩ := (IsCurveOver.hasPrincipalDivisors (K := L) (F := F)).exists_divisor g hg0
  have hratAll : ∀ P : Place L F, P.IsRational := fun P =>
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one P).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed P)
  have hdeg0 : Finsupp.degree Dg = 0 := by
    rw [← degree_eq_finsuppDegree Dg (fun P _ => hratAll P)]; exact hdegDg

  let piece : Place L F → Fin n ⊕ Fin m := fun P =>
    if h : ∃ i, P ∈ (C i).dom then Sum.inl h.choose
    else if h' : ∃ e, P ∈ (An e).dom then Sum.inr h'.choose else Sum.inl i₀
  have hpc : ∀ (P : Place L F) (i : Fin n), piece P = Sum.inl i ↔ P ∈ (C i).dom := by
    intro P i
    constructor
    · intro hpi
      by_cases h : ∃ i, P ∈ (C i).dom
      · have h1 : piece P = Sum.inl h.choose := by simp only [piece, dif_pos h]
        rw [h1, Sum.inl.injEq] at hpi
        rw [← hpi]; exact h.choose_spec
      · exfalso
        by_cases h' : ∃ e, P ∈ (An e).dom
        · have h1 : piece P = Sum.inr h'.choose := by simp only [piece, dif_neg h, dif_pos h']
          rw [h1] at hpi; exact Sum.inr_ne_inl hpi
        · rcases hcover P with ⟨l, hl, -, -⟩ | ⟨e, he, -, -⟩
          · exact h ⟨l, hl⟩
          · exact h' ⟨e, he⟩
    · intro hP
      have h : ∃ i, P ∈ (C i).dom := ⟨i, hP⟩
      have h1 : piece P = Sum.inl h.choose := by simp only [piece, dif_pos h]
      rw [h1, huniq h.choose_spec hP]
  have hpa : ∀ (P : Place L F) (e : Fin m), piece P = Sum.inr e ↔ P ∈ (An e).dom := by
    intro P e
    constructor
    · intro hpe
      by_cases h : ∃ i, P ∈ (C i).dom
      · have h1 : piece P = Sum.inl h.choose := by simp only [piece, dif_pos h]
        rw [h1] at hpe; exact absurd hpe Sum.inl_ne_inr
      · by_cases h' : ∃ e, P ∈ (An e).dom
        · have h1 : piece P = Sum.inr h'.choose := by simp only [piece, dif_neg h, dif_pos h']
          rw [h1, Sum.inr.injEq] at hpe
          rw [← hpe]; exact h'.choose_spec
        · have h1 : piece P = Sum.inl i₀ := by simp only [piece, dif_neg h, dif_neg h']
          rw [h1] at hpe; exact absurd hpe Sum.inl_ne_inr
    · intro hP
      rcases hcover P with ⟨l, hl, -, hno'⟩ | ⟨e', -, he', hno'⟩
      · exact absurd hP (hno' e)
      · have h : ¬ ∃ i, P ∈ (C i).dom := fun ⟨i, hi⟩ => hno' i hi
        have h' : ∃ e, P ∈ (An e).dom := ⟨e, hP⟩
        have h1 : piece P = Sum.inr h'.choose := by simp only [piece, dif_neg h, dif_pos h']
        rw [h1, he' _ h'.choose_spec, he' e hP]
  set ES : Finset (Fin m) := Finset.univ.filter fun e => src e ∈ S with hES
  set US : Finset (Fin n ⊕ Fin m) := S.image Sum.inl ∪ ES.image Sum.inr with hUS

  choose c hc hc0 using fun i => (C i).exists_smul_mem g hg0
  obtain ⟨ordAt, hordAt⟩ : ∃ o : (Σ l, Place (ResidueField A) (Fbar l)) → ℤ,
      ∀ l x, o ⟨l, x⟩ = x.ord ((C l).residue ⟨c l • g, hc l⟩) :=
    ⟨fun σ => σ.2.ord ((C σ.1).residue ⟨c σ.1 • g, hc σ.1⟩), fun _ _ => rfl⟩

  have hchart : ∀ i, ∑ P ∈ Dg.support.filter (fun P => piece P = Sum.inl i), Dg P =
      -∑ x ∈ (C i).nodes, ordAt ⟨i, x⟩ := by
    intro i
    have h1 : Dg.support.filter (fun P => piece P = Sum.inl i) = Dg.support.filter (fun P => P ∈ (C i).dom) :=
      Finset.filter_congr fun P _ => hpc P i
    rw [h1, ← degree_filter]
    have h2 := sum_nodes_ord_residue_eq_neg_degree (hratBar i) (C i) g hg0 (c i) (hc i) (hc0 i)
      (Dg.filter fun P => P ∈ (C i).dom)
      (fun P hP => by rw [Finsupp.filter_apply_pos _ _ hP, hDg P])
      (fun P hP => Finsupp.filter_apply_neg _ _ hP)
    have h3 : ∑ x ∈ (C i).nodes, ordAt ⟨i, x⟩ = ∑ x ∈ (C i).nodes, x.ord ((C i).residue ⟨c i • g, hc i⟩) :=
      Finset.sum_congr rfl fun x _ => hordAt i x
    rw [h3, h2, neg_neg]

  have hann : ∀ e, ∑ P ∈ Dg.support.filter (fun P => piece P = Sum.inr e), Dg P =
      ordAt ⟨src e, xs e⟩ + ordAt ⟨tgt e, xt e⟩ := by
    intro e
    have h1 : Dg.support.filter (fun P => piece P = Sum.inr e) = Dg.support.filter (fun P => P ∈ (An e).dom) :=
      Finset.filter_congr fun P _ => hpa P e
    rw [h1, ← degree_filter, ← sum_eq_degree, hordAt, hordAt]
    exact annulus_mass (An e) (An' e) (C (src e)) (C (tgt e)) (xs e) (xt e) (hpair e).1 (hpair e).2.2.1
      (hpair e).2.2.2 (hatt e).1 (hatt e).2 g hg0 (c (src e)) (hc (src e)) (hc0 (src e)) (c (tgt e))
      (hc (tgt e)) (hc0 (tgt e)) (Dg.filter fun P => P ∈ (An e).dom)
      (fun P hP => by
        rw [Finsupp.support_filter, Finset.mem_filter] at hP
        exact hP.2)
      (fun P hP => by rw [Finsupp.filter_apply_pos _ _ hP, hDg P])

  have hends : ∀ i, ∑ x ∈ (C i).nodes, ordAt ⟨i, x⟩ =
      (∑ e ∈ Finset.univ.filter (fun e => src e = i), ordAt ⟨src e, xs e⟩) +
        ∑ e ∈ Finset.univ.filter (fun e => tgt e = i), ordAt ⟨tgt e, xt e⟩ := fun i =>
    sum_nodes_eq_sum_ends (fun l => (C l).nodes) src tgt xs xt (fun e => (hatt e).1.1)
      (fun e => (hatt e).2.1) hnodes.1 hnodes.2 ordAt i
  have hET : Finset.univ.filter (fun e => tgt e ∈ S) = ES := by
    rw [hES]; exact Finset.filter_congr fun e _ => (hcl e).symm
  have hU0 : ∑ P ∈ Dg.support.filter (fun P => piece P ∈ US), Dg P = 0 := by
    rw [← Finset.sum_fiberwise_eq_sum_filter Dg.support US piece (fun P => Dg P)]
    have hdisj : Disjoint (S.image Sum.inl) (ES.image (Sum.inr : Fin m → Fin n ⊕ Fin m)) := by
      rw [Finset.disjoint_left]
      intro σ h1 h2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨e, -, he⟩ := Finset.mem_image.mp h2
      exact Sum.inr_ne_inl he
    rw [hUS, Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h => Sum.inl_injective h),
      Finset.sum_image (fun _ _ _ _ h => Sum.inr_injective h)]
    simp_rw [hchart, hann]
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
    simp_rw [hends]
    rw [Finset.sum_add_distrib, Finset.sum_fiberwise_eq_sum_filter Finset.univ S src (fun e => ordAt ⟨src e, xs e⟩),
      Finset.sum_fiberwise_eq_sum_filter Finset.univ S tgt (fun e => ordAt ⟨tgt e, xt e⟩), hET, ← hES]
    ring

  have hsplit := Finset.sum_filter_add_sum_filter_not Dg.support (fun P => piece P ∈ US) (fun P => Dg P)
  rw [hU0, zero_add, ← Finsupp.degree_apply] at hsplit

  have hP₀U : piece P₀ ∈ US := by
    rw [(hpc P₀ i₀).mpr hP₀, hUS, Finset.mem_union]
    exact Or.inl (Finset.mem_image_of_mem _ hi₀)
  have hP₁U : piece P₁ ∉ US := by
    rw [(hpc P₁ j).mpr hP₁, hUS, Finset.mem_union, not_or]
    constructor
    · intro h
      obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp h
      exact hj ((Sum.inl_injective hij) ▸ hi)
    · intro h
      obtain ⟨e, -, he⟩ := Finset.mem_image.mp h
      exact Sum.inr_ne_inl he
  have hnonneg : ∀ P ∈ Dg.support.filter (fun P => piece P ∉ US), 0 ≤ Dg P := by
    intro P hP
    have hP' := (Finset.mem_filter.mp hP).2
    have hne : P ≠ P₀ := fun h => hP' (h ▸ hP₀U)
    rw [hDg P]; exact hgreg P hne
  have hP₁mem : P₁ ∈ Dg.support.filter (fun P => piece P ∉ US) := by
    rw [Finset.mem_filter, Finsupp.mem_support_iff, hDg P₁]
    exact ⟨hgP₁.ne', hP₁U⟩
  have hle := Finset.single_le_sum hnonneg hP₁mem
  rw [hdeg0] at hsplit
  rw [hsplit, hDg P₁] at hle
  exact absurd hgP₁ (not_lt.mpr hle)

end

end S_AlgebraicCurve_SemistableCovering_exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne (solution)
