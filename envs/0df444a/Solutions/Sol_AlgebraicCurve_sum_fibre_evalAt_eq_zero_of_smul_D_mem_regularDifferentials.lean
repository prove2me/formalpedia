-- Prove2me | solution 1 for AlgebraicCurve.sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4890ab43-486b-52a3-abd4-d94aabf5c339

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_hasCanonicalLocalResidueK
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve KaehlerDifferential IntermediateField

namespace SumFibreTraceProof

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_iff_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  rw [v.mem_iff_adicValuation_le_one, v.adicValuation_le_one_iff, or_iff_right hf]

theorem residue_eq_zero_of_ord_pos (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : 0 < v.ord f) : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h0 := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at h0
  change v.ord f = 0 at h0
  omega

theorem ord_eq_zero_of_isUnit (v : Place K F) {a : v.toValuationSubring} (ha : IsUnit a) :
    v.ord (a : F) = 0 := by
  have h := v.ord_coe_unit ha.unit
  rwa [IsUnit.unit_spec] at h

theorem isRational_of_isCurveOver [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.IsRational := by
  haveI := IsCurveOver.finiteResidue v
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem local_simple_zero [∀ w : Place K F, w.DCoordGenerates] [Nontrivial (Ω[F⁄K])]
    (hreg : ∀ (w : Place K F) (u : F), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (D K F u) = 0 ∨ 0 ≤ w.ord (w.differentialCoeff (D K F u)))
    (v : Place K F) {g h e : F} (hg1 : v.ord g = 1) (he : e ∈ v.toValuationSubring)
    (hωe : h • D K F g = e • v.dCoord) :
    ∃ (hh : h ∈ v.toValuationSubring)
      (hm : v.uniformizer * (g⁻¹ * e) ∈ v.toValuationSubring),
      IsLocalRing.residue v.toValuationSubring ⟨v.uniformizer * (g⁻¹ * e), hm⟩
        = IsLocalRing.residue v.toValuationSubring ⟨h, hh⟩ := by
  have hπ0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  have hπ1 : v.ord v.uniformizer = 1 := v.ord_uniformizer
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [v.ord_zero] at hg1
    exact zero_ne_one hg1

  set w : F := g * v.uniformizer⁻¹ with hwdef
  have hw0 : w ≠ 0 := mul_ne_zero hg0 (inv_ne_zero hπ0)
  have hw : v.ord w = 0 := by
    rw [hwdef, v.ord_mul hg0 (inv_ne_zero hπ0), v.ord_inv, hg1, hπ1]; norm_num
  have hgw : g = w * v.uniformizer := by rw [hwdef, inv_mul_cancel_right₀ hπ0]
  have wmem : w ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hw0 hw.ge
  have wunit : IsUnit (⟨w, wmem⟩ : v.toValuationSubring) := v.isUnit_mk_of_ord_eq_zero hw0 hw

  set c : F := v.differentialCoeff (D K F w) with hcdef
  have hregc : c = 0 ∨ 0 ≤ v.ord c := hreg v w hw0 hw
  have hDw : D K F w = c • v.dCoord := (v.differentialCoeff_smul_dCoord _).symm
  have hDg : D K F g = (w + v.uniformizer * c) • v.dCoord := by
    rw [hgw, Derivation.leibniz, hDw, smul_smul, ← v.dCoord_eq, add_smul]
  have ha : v.differentialCoeff (D K F g) = w + v.uniformizer * c :=
    v.differentialCoeff_unique hDg
  have pcmem : v.uniformizer * c ∈ v.toValuationSubring := by
    rcases eq_or_ne c 0 with hc0 | hc0
    · rw [hc0, mul_zero]; exact zero_mem _
    · have hc := hregc.resolve_left hc0
      refine v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hπ0 hc0) ?_
      rw [v.ord_mul hπ0 hc0, hπ1]; omega
  have pcres : IsLocalRing.residue v.toValuationSubring ⟨v.uniformizer * c, pcmem⟩ = 0 := by
    rcases eq_or_ne c 0 with hc0 | hc0
    · have h0 : (⟨v.uniformizer * c, pcmem⟩ : v.toValuationSubring) = 0 := by
        apply Subtype.ext
        rw [ZeroMemClass.coe_zero]
        show v.uniformizer * c = 0
        rw [hc0, mul_zero]
      rw [h0, map_zero]
    · have hc := hregc.resolve_left hc0
      refine residue_eq_zero_of_ord_pos v pcmem ?_
      rw [v.ord_mul hπ0 hc0, hπ1]; omega
  have amem : w + v.uniformizer * c ∈ v.toValuationSubring := add_mem wmem pcmem
  have hares : IsLocalRing.residue v.toValuationSubring ⟨w + v.uniformizer * c, amem⟩
      = IsLocalRing.residue v.toValuationSubring ⟨w, wmem⟩ := by
    have hsplit : (⟨w + v.uniformizer * c, amem⟩ : v.toValuationSubring)
        = ⟨w, wmem⟩ + ⟨v.uniformizer * c, pcmem⟩ := by
      apply Subtype.ext
      rw [AddMemClass.coe_add]
    rw [hsplit, map_add, pcres, add_zero]
  have aunit : IsUnit (⟨w + v.uniformizer * c, amem⟩ : v.toValuationSubring) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hares, IsLocalRing.residue_ne_zero_iff_isUnit]
    exact wunit
  have ha0 : w + v.uniformizer * c ≠ 0 := by
    intro h0
    apply aunit.ne_zero
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact h0
  have horda : v.ord (w + v.uniformizer * c) = 0 := by

    have h' := ord_eq_zero_of_isUnit v aunit
    exact h'

  have hcoef1 : v.differentialCoeff (h • D K F g) = e := v.differentialCoeff_unique hωe
  have hcoef2 : v.differentialCoeff (h • D K F g) = h * (w + v.uniformizer * c) := by
    rw [v.differentialCoeff_smul, ha]
  have heq : h * (w + v.uniformizer * c) = e := hcoef2.symm.trans hcoef1

  have hh : h ∈ v.toValuationSubring := by
    rcases eq_or_ne h 0 with hh0 | hh0
    · rw [hh0]; exact zero_mem _
    · have he0 : e ≠ 0 := by rw [← heq]; exact mul_ne_zero hh0 ha0
      have horde : 0 ≤ v.ord e := (mem_iff_ord_nonneg v he0).mp he
      refine (mem_iff_ord_nonneg v hh0).mpr ?_
      have hord := congrArg v.ord heq
      rw [v.ord_mul hh0 ha0, horda, add_zero] at hord
      rw [hord]; exact horde

  have hwinv_mem : w⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hw0) (by rw [v.ord_inv, hw, neg_zero])
  have hπge : v.uniformizer * (g⁻¹ * e) = w⁻¹ * e := by
    rw [hgw, mul_inv, mul_comm w⁻¹, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul]
  have hm : v.uniformizer * (g⁻¹ * e) ∈ v.toValuationSubring := by
    rw [hπge]; exact mul_mem hwinv_mem he
  refine ⟨hh, hm, ?_⟩

  have hXW : (⟨v.uniformizer * (g⁻¹ * e), hm⟩ : v.toValuationSubring) * ⟨w, wmem⟩
      = ⟨h, hh⟩ * ⟨w + v.uniformizer * c, amem⟩ := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul]
    show v.uniformizer * (g⁻¹ * e) * w = h * (w + v.uniformizer * c)
    rw [heq, hπge, mul_comm w⁻¹ e, mul_assoc, inv_mul_cancel₀ hw0, mul_one]
  have hres := congrArg (IsLocalRing.residue v.toValuationSubring) hXW
  rw [map_mul, map_mul, hares] at hres
  exact mul_right_cancel₀ ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr wunit) hres

theorem finsum_trace_res_eq_zero [IsAlgClosed K]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] [IsCurveOver K F] [HasCanonicalLocalResidueKStar K F]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (a : F) :
    ∑ᶠ v : Place K F, Algebra.trace K v.ResidueField
        ((HasCanonicalLocalResidueKStar.dataKStar v).res (a * v.differentialCoeff ω)) = 0 := by
  classical
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  haveI : IsCurveOver K (RatFunc K) := AlgebraicCurve.isCurveOver_ratFunc K
  haveI : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  haveI : Algebra.EssFiniteType K (RatFunc K) :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  haveI : ∀ u : Place K (RatFunc K), u.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRT : ResidueTheoremK K F := AlgebraicCurve.residueTheoremK_of_isAlgClosed
  have h := hRT HasCanonicalLocalResidueKStar.dataKStar hω a
  rw [weilOfKaehlerK_apply] at h
  refine Eq.trans (finsum_congr fun v => ?_) h
  rw [kaehlerResidueTermKFam_apply]
  rfl

theorem main [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (f h : F) (hω : h • D K F f ∈ regularDifferentials K F) (t : K)
    (hsimple : ∀ v : Place K F,
      0 < v.ord (f - algebraMap K F t) → v.ord (f - algebraMap K F t) = 1)
    (Z : Finset (Place K F)) (hZ : ∀ v : Place K F, v ∈ Z ↔ 0 < v.ord (f - algebraMap K F t)) :
    ∑ v ∈ Z, v.evalAt h = 0 := by
  classical
  set g : F := f - algebraMap K F t with hgdef

  rcases eq_or_ne g 0 with hg0 | hg0
  · have hZe : Z = ∅ := Finset.eq_empty_of_forall_notMem fun v hv => by
      have hpos := (hZ v).mp hv
      rw [hg0, v.ord_zero] at hpos
      exact lt_irrefl _ hpos
    rw [hZe, Finset.sum_empty]
  obtain ⟨x, hx, hfd⟩ := hfg
  haveI := hfd

  haveI : Algebra.EssFiniteType K F :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
  haveI hgen : ∀ w : Place K F, w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hreg := AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver (K := K) (F' := F)
  have hrat : ∀ v : Place K F, v.IsRational := fun v => isRational_of_isCurveOver v

  have hDg : D K F g = D K F f := by
    rw [hgdef, map_sub, Derivation.map_algebraMap, sub_zero]
  have hωv : ∀ v : Place K F, ∃ e ∈ v.toValuationSubring, h • D K F g = e • v.dCoord := by
    intro v
    rw [hDg]
    exact (mem_regularDifferentials_iff.mp hω) v
  choose e he hωe using hωv
  have hcoef : ∀ v : Place K F, v.differentialCoeff (h • D K F f) = e v := fun v =>
    v.differentialCoeff_unique (by rw [← hDg]; exact hωe v)
  have hZ1 : ∀ v ∈ Z, v.ord g = 1 := fun v hv => hsimple v ((hZ v).mp hv)
  have hloc : ∀ v ∈ Z, ∃ (hh : h ∈ v.toValuationSubring)
      (hm : v.uniformizer * (g⁻¹ * e v) ∈ v.toValuationSubring),
      IsLocalRing.residue v.toValuationSubring ⟨v.uniformizer * (g⁻¹ * e v), hm⟩
        = IsLocalRing.residue v.toValuationSubring ⟨h, hh⟩ :=
    fun v hv => local_simple_zero hreg v (hZ1 v hv) (he v) (hωe v)
  by_cases hω0 : h • D K F f = 0
  ·
    refine Finset.sum_eq_zero fun v hv => ?_
    obtain ⟨hh, hm, hres⟩ := hloc v hv
    have he0 : e v = 0 := by rw [← hcoef v, hω0, v.differentialCoeff_zero]
    have hres0 : IsLocalRing.residue v.toValuationSubring ⟨h, hh⟩ = 0 := by
      rw [← hres]
      have h0 : (⟨v.uniformizer * (g⁻¹ * e v), hm⟩ : v.toValuationSubring) = 0 := by
        apply Subtype.ext
        rw [ZeroMemClass.coe_zero]
        show v.uniformizer * (g⁻¹ * e v) = 0
        rw [he0, mul_zero, mul_zero]
      rw [h0, map_zero]
    rw [v.evalAt_of_mem hh, hres0, ← map_zero (algebraMap K v.ResidueField),
      v.residueInv_algebraMap]
  ·
    haveI : HasCanonicalDivisor (K := K) (F := F) :=
      AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

    haveI : Algebra.IsSeparable K⟮x⟯ F := inferInstance
    set ex : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x hx with hex
    letI : Algebra (RatFunc K) F := ((algebraMap K⟮x⟯ F).comp ex.toAlgHom.toRingHom).toAlgebra
    have hsq : RingHom.comp (algebraMap (RatFunc K) F) (ex.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
        = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
      refine RingHom.ext fun a => ?_
      show algebraMap K⟮x⟯ F (ex (ex.symm a)) = algebraMap K⟮x⟯ F a
      rw [ex.apply_symm_apply]
    haveI : IsScalarTower K (RatFunc K) F :=
      IsScalarTower.of_algebraMap_eq fun a => by
        show algebraMap K F a = algebraMap K⟮x⟯ F (ex (algebraMap K (RatFunc K) a))
        rw [ex.commutes, ← IsScalarTower.algebraMap_apply]
    haveI : Module.Finite (RatFunc K) F :=
      Module.Finite.of_equiv_equiv ex.symm.toRingEquiv (RingEquiv.refl F) hsq
    haveI : Algebra.IsSeparable (RatFunc K) F :=
      Algebra.IsSeparable.of_equiv_equiv ex.symm.toRingEquiv (RingEquiv.refl F) hsq

    letI : HasCanonicalLocalResidueKStar K F :=
      ⟨fun v => Classical.choice ((AlgebraicCurve.hasCanonicalLocalResidueK K F).exists_data v)⟩
    set Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK :=
      HasCanonicalLocalResidueKStar.dataKStar with hRfam
    have hsum := finsum_trace_res_eq_zero (K := K) (F := F) hω0 g⁻¹

    set T : Place K F → K := fun v => Algebra.trace K v.ResidueField
      ((Rfam v).res (g⁻¹ * v.differentialCoeff (h • D K F f))) with hT
    change ∑ᶠ v, T v = 0 at hsum
    have hT_out : ∀ v : Place K F, v ∉ Z → T v = 0 := by
      intro v hv
      have hord : v.ord g ≤ 0 := by
        by_contra hcon
        push Not at hcon
        exact hv ((hZ v).mpr hcon)
      have hmem : g⁻¹ * e v ∈ v.toValuationSubring :=
        mul_mem (v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hg0)
          (by rw [v.ord_inv]; omega)) (he v)
      show Algebra.trace K v.ResidueField
        ((Rfam v).res (g⁻¹ * v.differentialCoeff (h • D K F f))) = 0
      rw [hcoef v, (Rfam v).res_of_mem _ hmem, map_zero]
    have hT_in : ∀ v ∈ Z, T v = v.evalAt h := by
      intro v hv
      obtain ⟨hh, hm, hres⟩ := hloc v hv
      show Algebra.trace K v.ResidueField
        ((Rfam v).res (g⁻¹ * v.differentialCoeff (h • D K F f))) = v.evalAt h
      rw [hcoef v, (Rfam v).res_simplePole _ hm, hres, ← v.algebraMap_evalAt (hrat v) hh,
        Algebra.trace_algebraMap,
        show Module.finrank K v.ResidueField = 1 from IsCurveOver.deg_eq_one_of_isAlgClosed v,
        one_smul]
    have hsupp : Function.support T ⊆ ↑Z := by
      intro v hv
      by_contra hcon
      exact hv (hT_out v hcon)
    rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum
    rw [← hsum]
    exact Finset.sum_congr rfl fun v hv => (hT_in v hv).symm

end SumFibreTraceProof

theorem solution
    (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (f h : F) (hω : h • KaehlerDifferential.D K F f ∈ regularDifferentials K F)
    (t : K)
    (hsimple : ∀ v : Place K F,
      0 < v.ord (f - algebraMap K F t) → v.ord (f - algebraMap K F t) = 1)
    (Z : Finset (Place K F)) (hZ : ∀ v : Place K F, v ∈ Z ↔ 0 < v.ord (f - algebraMap K F t)) :
    ∑ v ∈ Z, v.evalAt h = 0 :=
  SumFibreTraceProof.main hfg f h hω t hsimple Z hZ

end
end S_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials
end P2MW
export P2MW.S_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials (solution)
