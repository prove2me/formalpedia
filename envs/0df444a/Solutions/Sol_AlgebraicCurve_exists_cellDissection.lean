-- Prove2me | solution 1 for AlgebraicCurve.exists_cellDissection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/58ee75aa-f255-5c89-b19d-9d1f34e1130a

import Mathlib
import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Theorems.Thm_AlgebraicCurve_exists_pairedCellFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_cellDissection
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option Elab.async false

set_option autoImplicit false

open AlgebraicCurve Set
open scoped Manifold ContDiff Topology

namespace PairedCellFamily

variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
variable [ChartedSpace ℂ (Place ℂ F)]

section Compact

open Complex
open scoped Real

theorem periodic_apply_arg {r : ℝ → ℝ} (hper : Function.Periodic r (2 * π)) {t : ℝ} (ht : 0 < t)
    (φ : ℝ) : r (arg ((t : ℂ) * exp (φ * I))) = r φ := by
  rw [arg_real_mul _ ht, arg_exp_mul_I, toIocMod]
  exact hper.sub_zsmul_eq _

variable (R : RadialRegion)

theorem K_eq_image : R.K = (fun p : ℝ × ℝ => R.q + ((p.2 * R.r p.1 : ℝ) : ℂ) * exp (p.1 * I)) ''
    (Icc 0 (2 * π) ×ˢ Icc (0 : ℝ) 1) := by
  ext z
  constructor
  · intro hz
    have hz' : ‖z - R.q‖ ≤ R.r (arg (z - R.q)) := hz
    set φ₀ := arg (z - R.q) with hφ₀
    have hr0 : 0 < R.r φ₀ := R.hpos φ₀
    set t : ℝ := ‖z - R.q‖ / R.r φ₀ with ht
    have ht0 : 0 ≤ t := div_nonneg (norm_nonneg _) hr0.le
    have ht1 : t ≤ 1 := (div_le_one hr0).2 hz'

    set φ : ℝ := if φ₀ < 0 then φ₀ + 2 * π else φ₀ with hφ
    have hφI : φ ∈ Icc 0 (2 * π) := by
      have h1 := neg_pi_lt_arg (z - R.q)
      have h2 := arg_le_pi (z - R.q)
      simp only [hφ]
      split_ifs with h
      · constructor <;> linarith [Real.pi_pos]
      · constructor <;> linarith [Real.pi_pos]
    have hrφ : R.r φ = R.r φ₀ := by
      simp only [hφ]; split_ifs
      · exact R.hper φ₀
      · rfl
    have heφ : exp (φ * I) = exp (φ₀ * I) := by
      simp only [hφ]; split_ifs
      · rw [show ((φ₀ + 2 * π : ℝ) : ℂ) * I = φ₀ * I + 2 * π * I by push_cast; ring,
          exp_add, exp_two_pi_mul_I, mul_one]
      · rfl
    refine ⟨(φ, t), ⟨hφI, ht0, ht1⟩, ?_⟩
    show R.q + ((t * R.r φ : ℝ) : ℂ) * exp (φ * I) = z
    rw [hrφ, heφ, ht, div_mul_cancel₀ _ hr0.ne']
    have := norm_mul_exp_arg_mul_I (z - R.q)
    linear_combination this
  · rintro ⟨⟨φ, t⟩, ⟨hφ, ht0, ht1⟩, rfl⟩
    dsimp only at hφ ht0 ht1
    show ‖R.q + ((t * R.r φ : ℝ) : ℂ) * exp (φ * I) - R.q‖ ≤
      R.r (arg (R.q + ((t * R.r φ : ℝ) : ℂ) * exp (φ * I) - R.q))
    rw [add_sub_cancel_left]
    have hr0 : 0 < R.r φ := R.hpos φ
    rcases ht0.lt_or_eq with ht | ht
    · have hpos : 0 < t * R.r φ := mul_pos ht hr0
      rw [periodic_apply_arg R.hper hpos, norm_mul, norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      nlinarith
    · rw [← ht]
      simp only [zero_mul, ofReal_zero, norm_zero]
      exact (R.hpos _).le

theorem isCompact_K : IsCompact R.K := by
  rw [K_eq_image]
  refine (isCompact_Icc.prod isCompact_Icc).image ?_
  have hc := R.hcont
  fun_prop

end Compact

structure CellFamily (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] where

  IdxC : Type
  [instFintype : Fintype IdxC]

  cellOf : IdxC → Cell F

attribute [scoped instance] CellFamily.instFintype

namespace CellFamily

variable (A : CellFamily F)

noncomputable scoped instance : DecidableEq A.IdxC := Classical.decEq _

def ArcIdx : Type _ := Σ C : A.IdxC, Fin (A.cellOf C).R.N

noncomputable scoped instance : Fintype A.ArcIdx := by
  unfold ArcIdx
  infer_instance

noncomputable scoped instance : DecidableEq A.ArcIdx := Classical.decEq _

noncomputable def endPt (a : A.ArcIdx) (b : Bool) : Place ℂ F :=
  (A.cellOf a.1).bdry ((A.cellOf a.1).R.φs (if b then a.2.succ else a.2.castSucc))

theorem endPt_false (a : A.ArcIdx) :
    A.endPt a false = (A.cellOf a.1).bdry ((A.cellOf a.1).R.φs a.2.castSucc) := rfl

theorem endPt_true (a : A.ArcIdx) :
    A.endPt a true = (A.cellOf a.1).bdry ((A.cellOf a.1).R.φs a.2.succ) := rfl

def VertSet : Set (Place ℂ F) :=
  Set.range fun ab : A.ArcIdx × Bool => A.endPt ab.1 ab.2

theorem endPt_mem_vertSet (a : A.ArcIdx) (b : Bool) : A.endPt a b ∈ A.VertSet :=
  ⟨(a, b), rfl⟩

theorem vertSet_finite : A.VertSet.Finite := Set.finite_range _

def IdxV : Type _ := {v : Place ℂ F // v ∈ A.VertSet}

noncomputable scoped instance : Fintype A.IdxV := A.vertSet_finite.fintype

noncomputable scoped instance : DecidableEq A.IdxV := Classical.decEq _

def vert : A.IdxV → Place ℂ F := Subtype.val

theorem vert_injective : Function.Injective A.vert := Subtype.val_injective

end CellFamily
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.CellFamily"

structure EdgeData (A : CellFamily F) where
  pair : A.ArcIdx → A.ArcIdx
  hpair : ∀ a, pair (pair a) = a
  orient : A.ArcIdx → Bool
  horient : ∀ a, orient (pair a) = !orient a
  hrev : ∀ (C : A.IdxC) (k : Fin (A.cellOf C).R.N) (C' : A.IdxC)
    (k' : Fin (A.cellOf C').R.N),
    pair ⟨C, k⟩ = ⟨C', k'⟩ → orient ⟨C, k⟩ = true →
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((A.cellOf C').R.arcIcc k') ∧
      ContDiffOn ℝ 1 ψ ((A.cellOf C').R.arcIcc k') ∧
      ψ ((A.cellOf C').R.φs k'.castSucc) = (A.cellOf C).R.φs k.succ ∧
      ψ ((A.cellOf C').R.φs k'.succ) = (A.cellOf C).R.φs k.castSucc ∧
      ∀ t ∈ (A.cellOf C').R.arcIcc k', (A.cellOf C').bdry t = (A.cellOf C).bdry (ψ t)

namespace EdgeData

variable {A : CellFamily F} (E : EdgeData A)

theorem orient_pair_of_not {a : A.ArcIdx} (h : ¬E.orient a = true) :
    E.orient (E.pair a) = true := by
  have h' : E.orient a = false := by
    revert h
    cases E.orient a <;> simp
  rw [E.horient, h']
  rfl

def IdxE : Type _ := {a : A.ArcIdx // E.orient a = true}

noncomputable scoped instance : Fintype E.IdxE := by
  unfold IdxE
  infer_instance

noncomputable scoped instance : DecidableEq E.IdxE := Classical.decEq _

noncomputable def sideOf (C : A.IdxC) (k : Fin (A.cellOf C).R.N) : E.IdxE × Bool :=
  if h : E.orient ⟨C, k⟩ = true then (⟨⟨C, k⟩, h⟩, true)
  else (⟨E.pair ⟨C, k⟩, E.orient_pair_of_not h⟩, false)

theorem sideOf_bij :
    Function.Bijective fun a : A.ArcIdx => E.sideOf a.1 a.2 := by
  constructor
  · rintro ⟨C, k⟩ ⟨C', k'⟩ h
    simp only [sideOf] at h
    by_cases ha : E.orient ⟨C, k⟩ = true <;> by_cases ha' : E.orient ⟨C', k'⟩ = true
    · rw [dif_pos ha, dif_pos ha'] at h
      exact Subtype.ext_iff.mp (congrArg Prod.fst h)
    · rw [dif_pos ha, dif_neg ha'] at h
      exact Bool.noConfusion (congrArg Prod.snd h)
    · rw [dif_neg ha, dif_pos ha'] at h
      exact Bool.noConfusion (congrArg Prod.snd h)
    · rw [dif_neg ha, dif_neg ha'] at h
      have hval : E.pair ⟨C, k⟩ = E.pair ⟨C', k'⟩ :=
        Subtype.ext_iff.mp (congrArg Prod.fst h)
      have h2 := congrArg E.pair hval
      rwa [E.hpair, E.hpair] at h2
  · rintro ⟨e, b⟩
    cases b
    · rcases hpe : E.pair e.1 with ⟨C, k⟩
      refine ⟨⟨C, k⟩, ?_⟩
      show E.sideOf C k = (e, false)
      have ha : ¬E.orient ⟨C, k⟩ = true := by
        rw [← hpe, E.horient, e.2]
        simp
      unfold sideOf
      rw [dif_neg ha]
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      show E.pair ⟨C, k⟩ = e.1
      rw [← hpe, E.hpair]
    · rcases he1 : e.1 with ⟨C, k⟩
      refine ⟨⟨C, k⟩, ?_⟩
      show E.sideOf C k = (e, true)
      have ha : E.orient ⟨C, k⟩ = true := he1 ▸ e.2
      unfold sideOf
      rw [dif_pos ha]
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      show (⟨C, k⟩ : A.ArcIdx) = e.1
      exact he1.symm

theorem endPt_pair {a a' : A.ArcIdx} (hpa : E.pair a = a') (ha : E.orient a = true) :
    A.endPt a' false = A.endPt a true ∧ A.endPt a' true = A.endPt a false := by
  obtain ⟨ψ, -, -, hstart, hend, hpt⟩ := E.hrev a.1 a.2 a'.1 a'.2 hpa ha
  have hmemL : (A.cellOf a'.1).R.φs a'.2.castSucc ∈ (A.cellOf a'.1).R.arcIcc a'.2 :=
    Set.left_mem_Icc.mpr ((A.cellOf a'.1).R.hmono Fin.castSucc_lt_succ).le
  have hmemR : (A.cellOf a'.1).R.φs a'.2.succ ∈ (A.cellOf a'.1).R.arcIcc a'.2 :=
    Set.right_mem_Icc.mpr ((A.cellOf a'.1).R.hmono Fin.castSucc_lt_succ).le
  constructor
  · rw [A.endPt_false, A.endPt_true, hpt _ hmemL, hstart]
  · rw [A.endPt_true, A.endPt_false, hpt _ hmemR, hend]

noncomputable def endsOf (e : E.IdxE) : A.IdxV × A.IdxV :=
  (⟨A.endPt e.1 false, A.endPt_mem_vertSet _ _⟩, ⟨A.endPt e.1 true, A.endPt_mem_vertSet _ _⟩)

theorem arc_ends' (C : A.IdxC) (k : Fin (A.cellOf C).R.N) :
    (A.cellOf C).bdry ((A.cellOf C).R.φs k.castSucc) =
        A.vert (if (E.sideOf C k).2 then (E.endsOf (E.sideOf C k).1).1
          else (E.endsOf (E.sideOf C k).1).2) ∧
      (A.cellOf C).bdry ((A.cellOf C).R.φs k.succ) =
        A.vert (if (E.sideOf C k).2 then (E.endsOf (E.sideOf C k).1).2
          else (E.endsOf (E.sideOf C k).1).1) := by
  unfold sideOf
  split
  · exact ⟨rfl, rfl⟩
  · next h =>
      obtain ⟨h1, h2⟩ := E.endPt_pair (E.hpair ⟨C, k⟩) (E.orient_pair_of_not h)
      exact ⟨h1, h2⟩

theorem arc_rev' (C : A.IdxC) (k : Fin (A.cellOf C).R.N) (C' : A.IdxC)
    (k' : Fin (A.cellOf C').R.N)
    (he : (E.sideOf C k).1 = (E.sideOf C' k').1) (h2 : (E.sideOf C k).2 = true)
    (h2' : (E.sideOf C' k').2 = false) :
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((A.cellOf C').R.arcIcc k') ∧
      ContDiffOn ℝ 1 ψ ((A.cellOf C').R.arcIcc k') ∧
      ψ ((A.cellOf C').R.φs k'.castSucc) = (A.cellOf C).R.φs k.succ ∧
      ψ ((A.cellOf C').R.φs k'.succ) = (A.cellOf C).R.φs k.castSucc ∧
      ∀ t ∈ (A.cellOf C').R.arcIcc k', (A.cellOf C').bdry t = (A.cellOf C).bdry (ψ t) := by
  by_cases hCk : E.orient ⟨C, k⟩ = true
  · by_cases hCk' : E.orient ⟨C', k'⟩ = true
    · exfalso
      have : (E.sideOf C' k').2 = true := by
        unfold sideOf
        rw [dif_pos hCk']
      rw [this] at h2'
      exact Bool.noConfusion h2'
    · have he' : (⟨(⟨C, k⟩ : A.ArcIdx), hCk⟩ : E.IdxE) =
          ⟨E.pair ⟨C', k'⟩, E.orient_pair_of_not hCk'⟩ := by
        have hL : (E.sideOf C k).1 = ⟨(⟨C, k⟩ : A.ArcIdx), hCk⟩ := by
          unfold sideOf
          rw [dif_pos hCk]
        have hR : (E.sideOf C' k').1 = ⟨E.pair ⟨C', k'⟩, E.orient_pair_of_not hCk'⟩ := by
          unfold sideOf
          rw [dif_neg hCk']
        rw [← hL, ← hR]
        exact he
      have hval : (⟨C, k⟩ : A.ArcIdx) = E.pair ⟨C', k'⟩ := Subtype.ext_iff.mp he'
      have hpk : E.pair ⟨C, k⟩ = ⟨C', k'⟩ := by
        rw [hval, E.hpair]
      exact E.hrev C k C' k' hpk hCk
  · exfalso
    have : (E.sideOf C k).2 = false := by
      unfold sideOf
      rw [dif_neg hCk]
    rw [this] at h2
    exact Bool.noConfusion h2

theorem hends' (v : A.IdxV) :
    ∃ e : E.IdxE, (E.endsOf e).1 = v ∨ (E.endsOf e).2 = v := by
  obtain ⟨v, hv⟩ := v
  obtain ⟨⟨a, b⟩, hab⟩ := hv
  by_cases ha : E.orient a = true
  · refine ⟨⟨a, ha⟩, ?_⟩
    cases b
    · exact Or.inl (Subtype.ext hab)
    · exact Or.inr (Subtype.ext hab)
  · obtain ⟨h1, h2⟩ := E.endPt_pair (E.hpair a) (E.orient_pair_of_not ha)
    refine ⟨⟨E.pair a, E.orient_pair_of_not ha⟩, ?_⟩
    cases b
    · exact Or.inr (Subtype.ext (show A.endPt (E.pair a) true = v by rw [← h1]; exact hab))
    · exact Or.inl (Subtype.ext (show A.endPt (E.pair a) false = v by rw [← h2]; exact hab))

end EdgeData
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.CellFamily P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.EdgeData"

namespace CellFamily

variable (A : CellFamily F)

noncomputable def eqC : A.IdxC ≃ Fin (Fintype.card A.IdxC) := Fintype.equivFin _

noncomputable def eqV : A.IdxV ≃ Fin (Fintype.card A.IdxV) := Fintype.equivFin _

noncomputable def finCell (c : Fin (Fintype.card A.IdxC)) : Cell F :=
  A.cellOf (A.eqC.symm c)

noncomputable def finVert (v : Fin (Fintype.card A.IdxV)) : Place ℂ F :=
  A.vert (A.eqV.symm v)

theorem finVert_injective : Function.Injective A.finVert :=
  A.vert_injective.comp A.eqV.symm.injective

theorem finCell_cover (hcover : ∀ w : Place ℂ F, ∃ C : A.IdxC, w ∈ (A.cellOf C).carrier) :
    ⋃ c, (A.finCell c).carrier = Set.univ :=
  Set.iUnion_eq_univ_iff.mpr fun w => by
    obtain ⟨C, hC⟩ := hcover w
    refine ⟨A.eqC C, ?_⟩
    show w ∈ (A.cellOf (A.eqC.symm (A.eqC C))).carrier
    rw [Equiv.symm_apply_apply]
    exact hC

end CellFamily
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.CellFamily P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.EdgeData"

namespace EdgeData

variable {A : CellFamily F} (E : EdgeData A)

noncomputable def eqE : E.IdxE ≃ Fin (Fintype.card E.IdxE) := Fintype.equivFin _

noncomputable def finSide (c : Fin (Fintype.card A.IdxC)) (k : Fin (A.finCell c).R.N) :
    Fin (Fintype.card E.IdxE) × Bool :=
  (E.eqE (E.sideOf (A.eqC.symm c) k).1, (E.sideOf (A.eqC.symm c) k).2)

noncomputable def finEnds (e : Fin (Fintype.card E.IdxE)) :
    Fin (Fintype.card A.IdxV) × Fin (Fintype.card A.IdxV) :=
  (A.eqV (E.endsOf (E.eqE.symm e)).1, A.eqV (E.endsOf (E.eqE.symm e)).2)

theorem finSide_bij :
    Function.Bijective
      fun p : Σ c : Fin (Fintype.card A.IdxC), Fin (A.finCell c).R.N =>
        E.finSide p.1 p.2 := by
  have hΦ : Function.Bijective
      fun p : Σ c : Fin (Fintype.card A.IdxC), Fin (A.finCell c).R.N =>
        (⟨A.eqC.symm p.1, p.2⟩ : A.ArcIdx) :=
    (Equiv.sigmaCongrLeft (β := fun C : A.IdxC => Fin ((A.cellOf C).R.N))
      A.eqC.symm).bijective
  have hP : Function.Bijective fun q : E.IdxE × Bool => (E.eqE q.1, q.2) :=
    (E.eqE.prodCongr (Equiv.refl Bool)).bijective
  exact (hP.comp E.sideOf_bij).comp hΦ

theorem finSide_ends (c : Fin (Fintype.card A.IdxC)) (k : Fin (A.finCell c).R.N) :
    (A.finCell c).bdry ((A.finCell c).R.φs k.castSucc) =
        A.finVert (if (E.finSide c k).2 then (E.finEnds (E.finSide c k).1).1
          else (E.finEnds (E.finSide c k).1).2) ∧
      (A.finCell c).bdry ((A.finCell c).R.φs k.succ) =
        A.finVert (if (E.finSide c k).2 then (E.finEnds (E.finSide c k).1).2
          else (E.finEnds (E.finSide c k).1).1) := by
  obtain ⟨h1, h2⟩ := E.arc_ends' (A.eqC.symm c) k
  constructor
  · refine h1.trans ?_
    cases hb : (E.sideOf (A.eqC.symm c) k).2 <;>
      simp [CellFamily.finVert, finEnds, finSide, hb]
  · refine h2.trans ?_
    cases hb : (E.sideOf (A.eqC.symm c) k).2 <;>
      simp [CellFamily.finVert, finEnds, finSide, hb]

theorem finSide_rev (c : Fin (Fintype.card A.IdxC)) (k : Fin (A.finCell c).R.N)
    (c' : Fin (Fintype.card A.IdxC)) (k' : Fin (A.finCell c').R.N)
    (he : (E.finSide c k).1 = (E.finSide c' k').1) (h2 : (E.finSide c k).2 = true)
    (h2' : (E.finSide c' k').2 = false) :
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((A.finCell c').R.arcIcc k') ∧
      ContDiffOn ℝ 1 ψ ((A.finCell c').R.arcIcc k') ∧
      ψ ((A.finCell c').R.φs k'.castSucc) = (A.finCell c).R.φs k.succ ∧
      ψ ((A.finCell c').R.φs k'.succ) = (A.finCell c).R.φs k.castSucc ∧
      ∀ t ∈ (A.finCell c').R.arcIcc k', (A.finCell c').bdry t = (A.finCell c).bdry (ψ t) := by
  have he₀ : (E.sideOf (A.eqC.symm c) k).1 = (E.sideOf (A.eqC.symm c') k').1 :=
    E.eqE.injective he
  exact E.arc_rev' (A.eqC.symm c) k (A.eqC.symm c') k' he₀ h2 h2'

theorem sideOf_fst_eq_of_pair {C : A.IdxC} {k : Fin (A.cellOf C).R.N} {C' : A.IdxC}
    {k' : Fin (A.cellOf C').R.N} (hp : E.pair ⟨C, k⟩ = ⟨C', k'⟩) :
    (E.sideOf C k).1 = (E.sideOf C' k').1 := by
  have hor : E.orient ⟨C', k'⟩ = !E.orient ⟨C, k⟩ := by
    rw [← hp, E.horient]
  by_cases h : E.orient ⟨C, k⟩ = true
  · have h' : ¬E.orient ⟨C', k'⟩ = true := by
      rw [hor, h]
      simp
    unfold sideOf
    rw [dif_pos h, dif_neg h']
    apply Subtype.ext
    show (⟨C, k⟩ : A.ArcIdx) = E.pair ⟨C', k'⟩
    rw [← hp, E.hpair]
  · have h' : E.orient ⟨C', k'⟩ = true := by
      rw [hor]
      revert h
      cases E.orient ⟨C, k⟩ <;> simp
    unfold sideOf
    rw [dif_neg h, dif_pos h']
    apply Subtype.ext
    show E.pair ⟨C, k⟩ = (⟨C', k'⟩ : A.ArcIdx)
    exact hp

theorem finCell_inter
    (hinter : ∀ (C C' : A.IdxC) (x : Place ℂ F), x ∈ (A.cellOf C).carrier →
      x ∈ (A.cellOf C').carrier → Relation.ReflTransGen
        (fun X Y : A.IdxC => ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
          (E.sideOf X k).1 = (E.sideOf Y k').1 ∧ x ∈ (A.cellOf X).arc k) C C')
    (c c' : Fin (Fintype.card A.IdxC)) (x : Place ℂ F) (hc : x ∈ (A.finCell c).carrier)
    (hc' : x ∈ (A.finCell c').carrier) :
    Relation.ReflTransGen
      (fun a b : Fin (Fintype.card A.IdxC) =>
        ∃ (k : Fin (A.finCell a).R.N) (k' : Fin (A.finCell b).R.N),
          (E.finSide a k).1 = (E.finSide b k').1 ∧ x ∈ (A.finCell a).arc k) c c' := by
  have hmap : ∀ X Y : A.IdxC,
      (∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
        (E.sideOf X k).1 = (E.sideOf Y k').1 ∧ x ∈ (A.cellOf X).arc k) →
      ∃ (k₁ : Fin (A.finCell (A.eqC X)).R.N) (k₁' : Fin (A.finCell (A.eqC Y)).R.N),
        (E.finSide (A.eqC X) k₁).1 = (E.finSide (A.eqC Y) k₁').1 ∧
          x ∈ (A.finCell (A.eqC X)).arc k₁ := by
    intro X Y hXY
    obtain ⟨k, k', hkk', hxk⟩ := hXY
    unfold CellFamily.finCell finSide
    rw [A.eqC.symm_apply_apply, A.eqC.symm_apply_apply]
    exact ⟨k, k', congrArg E.eqE hkk', hxk⟩
  have h := Relation.ReflTransGen.lift
    (p := fun a b : Fin (Fintype.card A.IdxC) =>
      ∃ (k : Fin (A.finCell a).R.N) (k' : Fin (A.finCell b).R.N),
        (E.finSide a k).1 = (E.finSide b k').1 ∧ x ∈ (A.finCell a).arc k)
    A.eqC hmap _ _ (hinter (A.eqC.symm c) (A.eqC.symm c') x hc hc')
  simp only [Function.onFun, A.eqC.apply_symm_apply] at h
  exact h

theorem finCell_conn
    (hconn : ∀ C C' : A.IdxC, Relation.ReflTransGen
      (fun X Y : A.IdxC => ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
        (E.sideOf X k).1 = (E.sideOf Y k').1) C C')
    (c c' : Fin (Fintype.card A.IdxC)) :
    Relation.ReflTransGen
      (fun a b : Fin (Fintype.card A.IdxC) =>
        ∃ (k : Fin (A.finCell a).R.N) (k' : Fin (A.finCell b).R.N),
          (E.finSide a k).1 = (E.finSide b k').1) c c' := by
  have hmap : ∀ X Y : A.IdxC,
      (∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
        (E.sideOf X k).1 = (E.sideOf Y k').1) →
      ∃ (k₁ : Fin (A.finCell (A.eqC X)).R.N) (k₁' : Fin (A.finCell (A.eqC Y)).R.N),
        (E.finSide (A.eqC X) k₁).1 = (E.finSide (A.eqC Y) k₁').1 := by
    intro X Y hXY
    obtain ⟨k, k', hkk'⟩ := hXY
    unfold CellFamily.finCell finSide
    rw [A.eqC.symm_apply_apply, A.eqC.symm_apply_apply]
    exact ⟨k, k', congrArg E.eqE hkk'⟩
  have h := Relation.ReflTransGen.lift
    (p := fun a b : Fin (Fintype.card A.IdxC) =>
      ∃ (k : Fin (A.finCell a).R.N) (k' : Fin (A.finCell b).R.N),
        (E.finSide a k).1 = (E.finSide b k').1)
    A.eqC hmap _ _ (hconn (A.eqC.symm c) (A.eqC.symm c'))
  simp only [Function.onFun, A.eqC.apply_symm_apply] at h
  exact h

noncomputable def toDissection
    (hcover : ∀ w : Place ℂ F, ∃ C : A.IdxC, w ∈ (A.cellOf C).carrier)
    (hinter : ∀ (C C' : A.IdxC) (x : Place ℂ F), x ∈ (A.cellOf C).carrier →
      x ∈ (A.cellOf C').carrier → Relation.ReflTransGen
        (fun X Y : A.IdxC => ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
          (E.sideOf X k).1 = (E.sideOf Y k').1 ∧ x ∈ (A.cellOf X).arc k) C C')
    (hconn : ∀ C C' : A.IdxC, Relation.ReflTransGen
      (fun X Y : A.IdxC => ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
        (E.sideOf X k).1 = (E.sideOf Y k').1) C C') :
    CellDissection F where
  ιC := Fin (Fintype.card A.IdxC)
  ιE := Fin (Fintype.card E.IdxE)
  ιV := Fin (Fintype.card A.IdxV)
  cell := A.finCell
  side := E.finSide
  side_bij := E.finSide_bij
  ends := E.finEnds
  vert := A.finVert
  arc_ends := E.finSide_ends
  arc_rev := E.finSide_rev
  cover := A.finCell_cover hcover
  inter := E.finCell_inter hinter
  conn := E.finCell_conn hconn

def Adj (X Y : A.IdxC) : Prop :=
  ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N), E.pair ⟨X, k⟩ = ⟨Y, k'⟩

theorem reflTransGen_adj_of_star {x : Place ℂ F} {X Y : A.IdxC}
    (h : Relation.ReflTransGen
      (fun X Y : A.IdxC => ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
        E.pair ⟨X, k⟩ = ⟨Y, k'⟩ ∧ x ∈ (A.cellOf X).arc k) X Y) :
    Relation.ReflTransGen E.Adj X Y := by
  refine Relation.ReflTransGen.mono ?_ _ _ h
  rintro X' Y' ⟨k, k', hp, -⟩
  exact ⟨k, k', hp⟩

theorem isClosed_carrier [T2Space (Place ℂ F)] (C : Cell F) : IsClosed C.carrier :=
  ((isCompact_K C.R).image_of_continuousOn (C.ζ.continuousOn_symm.mono C.hKt)).isClosed

theorem carrier_nonempty (C : Cell F) : C.carrier.Nonempty := by
  refine ⟨C.ζ.symm C.R.q, C.R.q, ?_, rfl⟩
  show ‖C.R.q - C.R.q‖ ≤ C.R.r (Complex.arg (C.R.q - C.R.q))
  rw [sub_self, norm_zero]
  exact (C.R.hpos _).le

theorem conn_of_cover_inter [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hcover : ∀ w : Place ℂ F, ∃ C : A.IdxC, w ∈ (A.cellOf C).carrier)
    (hinter : ∀ (C C' : A.IdxC) (x : Place ℂ F), x ∈ (A.cellOf C).carrier →
      x ∈ (A.cellOf C').carrier → Relation.ReflTransGen
        (fun X Y : A.IdxC => ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
          E.pair ⟨X, k⟩ = ⟨Y, k'⟩ ∧ x ∈ (A.cellOf X).arc k) C C')
    (C C' : A.IdxC) :
    Relation.ReflTransGen
      (fun X Y : A.IdxC => ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
        E.pair ⟨X, k⟩ = ⟨Y, k'⟩) C C' := by
  classical
  set Reach : Set A.IdxC := {D | Relation.ReflTransGen E.Adj C D} with hReach
  set U : Set (Place ℂ F) := ⋃ D ∈ Reach, (A.cellOf D).carrier with hU
  set V : Set (Place ℂ F) := ⋃ D ∈ Reachᶜ, (A.cellOf D).carrier with hV
  have hUc : IsClosed U :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun D _ => isClosed_carrier (A.cellOf D)
  have hVc : IsClosed V :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun D _ => isClosed_carrier (A.cellOf D)
  have hdisj : ∀ x ∈ U, x ∉ V := by
    intro x hxU hxV
    obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp hxU
    obtain ⟨D', hD', hxD'⟩ := mem_iUnion₂.mp hxV
    exact hD' (Relation.ReflTransGen.trans hD
      (E.reflTransGen_adj_of_star (hinter D D' x hxD hxD')))
  have hcov : ∀ x : Place ℂ F, x ∈ U ∨ x ∈ V := by
    intro x
    obtain ⟨D, hxD⟩ := hcover x
    by_cases hD : D ∈ Reach
    · exact Or.inl (mem_iUnion₂.mpr ⟨D, hD, hxD⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨D, hD, hxD⟩)
  have hcompl : Uᶜ = V := by
    ext x
    constructor
    · intro hx
      exact (hcov x).resolve_left hx
    · intro hx hxU
      exact hdisj x hxU hx
  have hUo : IsOpen U := by
    rw [← isClosed_compl_iff, hcompl]
    exact hVc
  have hUne : U.Nonempty := by
    obtain ⟨x, hx⟩ := carrier_nonempty (A.cellOf C)
    exact ⟨x, mem_iUnion₂.mpr ⟨C, Relation.ReflTransGen.refl, hx⟩⟩
  have hUuniv : U = univ := IsClopen.eq_univ ⟨hUc, hUo⟩ hUne
  obtain ⟨x, hx⟩ := carrier_nonempty (A.cellOf C')
  have hxU : x ∈ U := by
    rw [hUuniv]
    exact mem_univ x
  obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp hxU
  show Relation.ReflTransGen E.Adj C C'
  exact Relation.ReflTransGen.trans hD (E.reflTransGen_adj_of_star (hinter D C' x hxD hx))

theorem vertSet_eq : A.VertSet = {v : Place ℂ F | ∃ (C : A.IdxC) (k : Fin (A.cellOf C).R.N),
    v = (A.cellOf C).bdry ((A.cellOf C).R.φs k.castSucc) ∨
      v = (A.cellOf C).bdry ((A.cellOf C).R.φs k.succ)} := by
  ext v
  constructor
  · rintro ⟨⟨⟨C, k⟩, b⟩, rfl⟩
    refine ⟨C, k, ?_⟩
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro ⟨C, k, h | h⟩
    · exact ⟨(⟨C, k⟩, false), h.symm⟩
    · exact ⟨(⟨C, k⟩, true), h.symm⟩

theorem card_idxV : Fintype.card A.IdxV = A.VertSet.ncard := by
  rw [Fintype.card_eq_nat_card]
  exact Nat.card_coe_set_eq _

theorem card_arcIdx : Fintype.card A.ArcIdx = ∑ C : A.IdxC, (A.cellOf C).R.N := by
  show Fintype.card (Σ C : A.IdxC, Fin (A.cellOf C).R.N) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]

noncomputable def posEquivNeg : E.IdxE ≃ {a : A.ArcIdx // ¬ E.orient a = true} where
  toFun a := ⟨E.pair a.1, by rw [E.horient, a.2]; simp⟩
  invFun a := ⟨E.pair a.1, by rw [E.horient]; simpa using a.2⟩
  left_inv a := Subtype.ext (E.hpair a.1)
  right_inv a := Subtype.ext (E.hpair a.1)

theorem two_mul_card_idxE : 2 * Fintype.card E.IdxE = Fintype.card A.ArcIdx := by
  classical
  have h1 : Fintype.card E.IdxE = Fintype.card {a : A.ArcIdx // E.orient a = true} :=
    Fintype.card_congr (Equiv.refl _)
  have h2 : Fintype.card E.IdxE = Fintype.card {a : A.ArcIdx // ¬ E.orient a = true} :=
    Fintype.card_congr E.posEquivNeg
  have h3 := Fintype.card_subtype_compl (fun a : A.ArcIdx => E.orient a = true)
  have h4 : Fintype.card {a : A.ArcIdx // E.orient a = true} ≤ Fintype.card A.ArcIdx :=
    Fintype.card_subtype_le _
  omega

theorem exists_cellDissection_of_data [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hcover : ∀ w : Place ℂ F, ∃ C : A.IdxC, w ∈ (A.cellOf C).carrier)
    (hinter : ∀ (C C' : A.IdxC) (x : Place ℂ F), x ∈ (A.cellOf C).carrier →
      x ∈ (A.cellOf C').carrier → Relation.ReflTransGen
        (fun X Y : A.IdxC => ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
          E.pair ⟨X, k⟩ = ⟨Y, k'⟩ ∧ x ∈ (A.cellOf X).arc k) C C')
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F))
    (hd1 : ∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : A.IdxC, v ∈ (A.cellOf C).interior')
    (hd2 : ∀ C : A.IdxC, ((A.cellOf C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (g : ℤ)
    (hd3 : 2 * ({v : Place ℂ F | ∃ (C : A.IdxC) (k : Fin (A.cellOf C).R.N),
        v = (A.cellOf C).bdry ((A.cellOf C).R.φs k.castSucc) ∨
          v = (A.cellOf C).bdry ((A.cellOf C).R.φs k.succ)}.ncard : ℤ)
        - (∑ C : A.IdxC, ((A.cellOf C).R.N : ℤ)) + 2 * (Fintype.card A.IdxC : ℤ)
        = 2 * (2 - 2 * g))
    (hd5 : ∀ v ∈ (S : Set (Place ℂ F)), ∃ C : A.IdxC,
      v ∈ (A.cellOf C).interior' ∧ (A.cellOf C).ζ v = (A.cellOf C).R.q) :
    ∃ 𝒟 : CellDissection F,
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior') ∧
      (∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      (Fintype.card 𝒟.ιV : ℤ) - (Fintype.card 𝒟.ιE : ℤ) + (Fintype.card 𝒟.ιC : ℤ)
        = 2 - 2 * g ∧
      (∀ v ∈ (S : Set (Place ℂ F)), ∃ C : 𝒟.ιC,
        v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q) ∧
      Function.Injective 𝒟.vert ∧
      (∀ v : 𝒟.ιV, ∃ e : 𝒟.ιE, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v) := by
  have hinter' : ∀ (C C' : A.IdxC) (x : Place ℂ F), x ∈ (A.cellOf C).carrier →
      x ∈ (A.cellOf C').carrier → Relation.ReflTransGen
        (fun X Y : A.IdxC => ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
          (E.sideOf X k).1 = (E.sideOf Y k').1 ∧ x ∈ (A.cellOf X).arc k) C C' := by
    intro C C' x hC hC'
    refine Relation.ReflTransGen.mono ?_ _ _ (hinter C C' x hC hC')
    rintro X Y ⟨k, k', hp, hx⟩
    exact ⟨k, k', E.sideOf_fst_eq_of_pair hp, hx⟩
  have hconn := E.conn_of_cover_inter hcover hinter
  have hconn' : ∀ C C' : A.IdxC, Relation.ReflTransGen
      (fun X Y : A.IdxC => ∃ (k : Fin (A.cellOf X).R.N) (k' : Fin (A.cellOf Y).R.N),
        (E.sideOf X k).1 = (E.sideOf Y k').1) C C' := by
    intro C C'
    refine Relation.ReflTransGen.mono ?_ _ _ (hconn C C')
    rintro X Y ⟨k, k', hp⟩
    exact ⟨k, k', E.sideOf_fst_eq_of_pair hp⟩
  refine ⟨E.toDissection hcover hinter' hconn', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨C, hC⟩ := hd1 v hv
    refine ⟨A.eqC C, ?_⟩
    show v ∈ (A.cellOf (A.eqC.symm (A.eqC C))).interior'
    rw [A.eqC.symm_apply_apply]
    exact hC
  · intro C
    exact hd2 (A.eqC.symm C)
  · show (Fintype.card (Fin (Fintype.card A.IdxV)) : ℤ)
      - (Fintype.card (Fin (Fintype.card E.IdxE)) : ℤ)
      + (Fintype.card (Fin (Fintype.card A.IdxC)) : ℤ) = 2 - 2 * g
    simp only [Fintype.card_fin]
    have hV : (Fintype.card A.IdxV : ℤ) = ({v : Place ℂ F | ∃ (C : A.IdxC) (k : Fin (A.cellOf C).R.N),
        v = (A.cellOf C).bdry ((A.cellOf C).R.φs k.castSucc) ∨
          v = (A.cellOf C).bdry ((A.cellOf C).R.φs k.succ)}.ncard : ℤ) := by
      rw [card_idxV (A := A), vertSet_eq (A := A)]
    have hE : (2 * Fintype.card E.IdxE : ℤ) = ∑ C : A.IdxC, ((A.cellOf C).R.N : ℤ) := by
      have h := E.two_mul_card_idxE
      rw [card_arcIdx (A := A)] at h
      exact_mod_cast h
    omega
  · intro v hv
    obtain ⟨C, hC1, hC2⟩ := hd5 v hv
    refine ⟨A.eqC C, ?_, ?_⟩
    · show v ∈ (A.cellOf (A.eqC.symm (A.eqC C))).interior'
      rw [A.eqC.symm_apply_apply]
      exact hC1
    · show (A.cellOf (A.eqC.symm (A.eqC C))).ζ v = (A.cellOf (A.eqC.symm (A.eqC C))).R.q
      rw [A.eqC.symm_apply_apply]
      exact hC2
  · exact A.finVert_injective
  · intro v
    obtain ⟨e, he⟩ := E.hends' (A.eqV.symm v)
    refine ⟨E.eqE e, ?_⟩
    rcases he with h | h
    · left
      show A.eqV (E.endsOf (E.eqE.symm (E.eqE e))).1 = v
      rw [E.eqE.symm_apply_apply, h, A.eqV.apply_symm_apply]
    · right
      show A.eqV (E.endsOf (E.eqE.symm (E.eqE e))).2 = v
      rw [E.eqE.symm_apply_apply, h, A.eqV.apply_symm_apply]

end EdgeData
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.CellFamily P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.EdgeData"

end PairedCellFamily
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.CellFamily P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily.EdgeData P2MW.S_AlgebraicCurve_exists_cellDissection.PairedCellFamily"

open PairedCellFamily in

theorem PairedCellFamily.exists_cellDissection_of_pairedCellFamily
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ 𝒟 : CellDissection F,
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior') ∧
      (∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      (Fintype.card 𝒟.ιV : ℤ) - (Fintype.card 𝒟.ιE : ℤ) + (Fintype.card 𝒟.ιC : ℤ)
        = 2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) ∧
      (∀ v ∈ (S : Set (Place ℂ F)), ∃ C : 𝒟.ιC,
        v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q) ∧
      Function.Injective 𝒟.vert ∧
      (∀ v : 𝒟.ιV, ∃ e : 𝒟.ιE, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v) := by
  obtain ⟨m, cell, pair, orient, hpair, horient, hrev, hcover, hinter, hd1, hd2, hd3, hd5⟩ :=
    AlgebraicCurve.exists_pairedCellFamily F hfg hF P₀ S
  let A : CellFamily F := { IdxC := Fin m, cellOf := cell }
  let E : EdgeData A := ⟨pair, hpair, orient, horient, hrev⟩
  have hcard : Fintype.card A.IdxC = m := Fintype.card_fin m
  have hd3' : 2 * ({v : Place ℂ F | ∃ (C : A.IdxC) (k : Fin (A.cellOf C).R.N),
        v = (A.cellOf C).bdry ((A.cellOf C).R.φs k.castSucc) ∨
          v = (A.cellOf C).bdry ((A.cellOf C).R.φs k.succ)}.ncard : ℤ)
        - (∑ C : A.IdxC, ((A.cellOf C).R.N : ℤ)) + 2 * (Fintype.card A.IdxC : ℤ)
        = 2 * (2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ)) := by
    rw [hcard]
    exact hd3
  exact E.exists_cellDissection_of_data hcover hinter P₀ S hd1 hd2 _ hd3' hd5

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ 𝒟 : CellDissection F,
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior') ∧
      (∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      (Fintype.card 𝒟.ιV : ℤ) - (Fintype.card 𝒟.ιE : ℤ) + (Fintype.card 𝒟.ιC : ℤ)
        = 2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) ∧
      (∀ v ∈ (S : Set (Place ℂ F)), ∃ C : 𝒟.ιC,
        v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q) ∧
      Function.Injective 𝒟.vert ∧
      (∀ v : 𝒟.ιV, ∃ e : 𝒟.ιE, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v) := by
  exact PairedCellFamily.exists_cellDissection_of_pairedCellFamily (F := F) (hfg := hfg) (hF := hF) (P₀ := P₀) (S := S)

end S_AlgebraicCurve_exists_cellDissection
end P2MW
export P2MW.S_AlgebraicCurve_exists_cellDissection (solution)
