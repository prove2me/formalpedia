-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.exists_equiv_placeMap_smul_eq_of_forall_mem_integers_iff_of_forall_mem_dom_iff_of_discFibres
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/46b88037-5f25-5545-968d-fe5621c7c0d1

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_exists_equiv_placeMap_smul_eq_of_forall_mem_integers_iff_of_forall_mem_dom_iff_of_discFibres
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

noncomputable section

namespace PMT

open scoped Classical

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap (v : Place K F) (c : K) (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  let u : v.toValuationSubringˣ :=
    ⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  exact v.ord_coe_unit u

private theorem _root_.PMT.ord_smul (v : Place K F) (c : K) (hc : c ≠ 0) (f : F) (hf : f ≠ 0) :
    v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).2 hc) hf, ord_algebraMap v c hc, zero_add]

p2m_export "PMT" "ord_smul"

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (r : α → β) (D : α →₀ ℤ) (b : β) :
    Finsupp.mapDomain r D b = ∑ a ∈ D.support with r a = b, D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem infinite_place [IsCurveOver K F] (v₀ : Place K F) : Infinite (Place K F) := by
  classical
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  haveI := Fintype.ofFinite (Place K F)
  obtain ⟨g, hg0, hg⟩ :=
    Place.exists_forall_ord_eq_finset (Finset.univ : Finset (Place K F)) (fun _ => (1 : ℤ))
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg0
  have hD1 : ∀ v, D v = 1 := fun v => by rw [hD v, hg v (Finset.mem_univ v)]
  have hDeq : D = ∑ v : Place K F, Finsupp.single v 1 := by
    ext v
    rw [hD1, Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply]
  have hdegv : ∀ v : Place K F, (1 : ℤ) ≤ v.deg := by
    intro v
    haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
    have : 0 < Module.finrank K v.ResidueField := Module.finrank_pos
    show (1 : ℤ) ≤ ((Module.finrank K v.ResidueField : ℕ) : ℤ)
    exact_mod_cast this
  have hpos : (1 : ℤ) ≤ Divisor.degree D := by
    rw [hDeq, map_sum]
    simp only [Divisor.degree_single, one_mul]
    calc (1 : ℤ) ≤ (v₀.deg : ℤ) := hdegv v₀
      _ ≤ ∑ v : Place K F, (v.deg : ℤ) :=
          Finset.single_le_sum (fun v _ => le_trans zero_le_one (hdegv v)) (Finset.mem_univ v₀)
  rw [hdeg] at hpos
  exact absurd hpos (by norm_num)

end General

section Core

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {k Fb : Type*} [Field k] [Field Fb] [Algebra k Fb]

structure Setup (K F k Fb : Type*) [Field K] [Field F] [Algebra K F] [Field k] [Field Fb] [Algebra k Fb] where
  dom : Set (Place K F)
  good : F → Fb → Prop
  r₁ : Place K F → Place k Fb
  r₂ : Place K F → Place k Fb
  N₁ : Finset (Place k Fb)
  N₂ : Finset (Place k Fb)
  good_ne : ∀ f g, good f g → f ≠ 0 ∧ g ≠ 0
  law₁ : ∀ f g, good f g → ∀ D : Divisor K F, (∀ P ∈ dom, D P = P.ord f) → (∀ P, P ∉ dom → D P = 0) →
    ∀ Q, Q ∉ N₁ → Finsupp.mapDomain r₁ D Q = Q.ord g
  law₂ : ∀ f g, good f g → ∀ D : Divisor K F, (∀ P ∈ dom, D P = P.ord f) → (∀ P, P ∉ dom → D P = 0) →
    ∀ Q, Q ∉ N₂ → Finsupp.mapDomain r₂ D Q = Q.ord g
  lift : ∀ g : Fb, g ≠ 0 → ∃ f, good f g
  scale : ∀ h : F, h ≠ 0 → ∃ f g, good f g ∧ ∀ v : Place K F, v.ord f = v.ord h
  not_mem₁ : ∀ P ∈ dom, r₁ P ∉ N₁
  not_mem₂ : ∀ P ∈ dom, r₂ P ∉ N₂
  surj₁ : ∀ Q, Q ∉ N₁ → ∃ P ∈ dom, r₁ P = Q
  surj₂ : ∀ Q, Q ∉ N₂ → ∃ P ∈ dom, r₂ P = Q

namespace Setup

def swap (S : Setup K F k Fb) : Setup K F k Fb where
  dom := S.dom
  good := S.good
  r₁ := S.r₂
  r₂ := S.r₁
  N₁ := S.N₂
  N₂ := S.N₁
  good_ne := S.good_ne
  law₁ := S.law₂
  law₂ := S.law₁
  lift := S.lift
  scale := S.scale
  not_mem₁ := S.not_mem₂
  not_mem₂ := S.not_mem₁
  surj₁ := S.surj₂
  surj₂ := S.surj₁

variable (S : Setup K F k Fb)

theorem exists_divisor [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    ∃ D : Divisor K F, (∀ P ∈ S.dom, D P = P.ord f) ∧ (∀ P, P ∉ S.dom → D P = 0) := by
  classical
  obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine ⟨D₀.filter (· ∈ S.dom), fun P hP => ?_, fun P hP => ?_⟩
  · rw [Finsupp.filter_apply_pos _ _ hP, hD₀]
  · rw [Finsupp.filter_apply_neg _ _ hP]

def psi [DecidablePred (· ∈ S.dom)] (r : Place K F → Place k Fb) (X : Place k Fb) : Divisor K F →+ ℤ :=
  (Finsupp.applyAddHom X).comp
    ((Finsupp.mapDomain.addMonoidHom r).comp (Finsupp.filterAddHom (· ∈ S.dom)))

theorem psi_apply [DecidablePred (· ∈ S.dom)] (r : Place K F → Place k Fb) (X : Place k Fb) (D : Divisor K F) :
    S.psi r X D = Finsupp.mapDomain r (D.filter (· ∈ S.dom)) X := rfl

theorem psi_single [DecidablePred (· ∈ S.dom)] [DecidableEq (Place k Fb)] (r : Place K F → Place k Fb)
    (X : Place k Fb) (P : Place K F) (hP : P ∈ S.dom) (c : ℤ) :
    S.psi r X (Finsupp.single P c) = if r P = X then c else 0 := by
  rw [psi_apply, Finsupp.filter_single_of_pos _ hP, Finsupp.mapDomain_single, Finsupp.single_apply]

theorem mem_of_ne [HasPrincipalDivisors K F] [Infinite (Place k Fb)]
    (hdeg : ∀ P : Place K F, P.deg = 1) (hdiv : ∀ y : Pic0 K F, ∃ z : Pic0 K F, 3 • z = y)
    (P₀ : Place K F) (hP₀ : P₀ ∈ S.dom) (hne : S.r₁ P₀ ≠ S.r₂ P₀) : S.r₁ P₀ ∈ S.N₂ := by
  classical
  by_contra hX₂
  set X := S.r₁ P₀ with hXdef
  have hX₁ : X ∉ S.N₁ := S.not_mem₁ P₀ hP₀

  obtain ⟨X₂, hX₂'⟩ := Infinite.exists_notMem_finset (insert X S.N₁)
  rw [Finset.mem_insert, not_or] at hX₂'
  obtain ⟨P₁, hP₁, hP₁X⟩ := S.surj₁ X₂ hX₂'.2
  have hr₁P₁ : S.r₁ P₁ ≠ X := by rw [hP₁X]; exact hX₂'.1

  set E : Divisor K F := Finsupp.single P₀ 1 - Finsupp.single P₁ 1 with hEdef
  have hE : E ∈ Divisor.degZero (K := K) (F := F) := by
    rw [Divisor.mem_degZero, hEdef, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]
    simp
  obtain ⟨z, hz⟩ := hdiv (Pic0.mk ⟨E, hE⟩)
  obtain ⟨E', rfl⟩ := Pic0.mk_surjective z
  have h3 : (3 : ℕ) • Pic0.mk E' = Pic0.mk (3 • E') := (QuotientAddGroup.mk_nsmul _ E' 3).symm
  rw [h3, Pic0.mk, Pic0.mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hz
  obtain ⟨h, hh0, hh⟩ := hz
  have hEv : ∀ v : Place K F, E v = 3 * (E' : Divisor K F) v + v.ord h := by
    intro v
    have := hh v
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroupClass.coe_nsmul, Finsupp.add_apply,
      Finsupp.neg_apply, Finsupp.smul_apply, nsmul_eq_mul] at this
    push_cast at this
    linarith

  obtain ⟨f, g, hfg, hford⟩ := S.scale h hh0
  obtain ⟨hf0, hg0⟩ := S.good_ne f g hfg
  obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hEeq : E = 3 • (E' : Divisor K F) + D₀ := by
    ext v
    rw [hEv v, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, hD₀ v, hford v]
    push_cast
    ring

  set Ψ : Divisor K F →+ ℤ := S.psi S.r₁ X - S.psi S.r₂ X with hΨdef
  have hΨD₀ : Ψ D₀ = 0 := by
    have hD : ∀ P ∈ S.dom, (D₀.filter (· ∈ S.dom)) P = P.ord f := fun P hP => by
      rw [Finsupp.filter_apply_pos _ _ hP, hD₀]
    have hD' : ∀ P, P ∉ S.dom → (D₀.filter (· ∈ S.dom)) P = 0 := fun P hP => by
      rw [Finsupp.filter_apply_neg _ _ hP]
    simp only [hΨdef, AddMonoidHom.sub_apply, psi_apply]
    rw [S.law₁ f g hfg _ hD hD' X hX₁, S.law₂ f g hfg _ hD hD' X hX₂, sub_self]
  have hΨE : Ψ E = 1 + (if S.r₂ P₁ = X then 1 else 0) := by
    simp only [hΨdef, hEdef, AddMonoidHom.sub_apply, map_sub, S.psi_single _ _ _ hP₀, S.psi_single _ _ _ hP₁]
    rw [if_pos rfl, if_neg hr₁P₁, if_neg (Ne.symm hne)]
    split_ifs <;> ring
  have hkey : Ψ E = 3 * Ψ (E' : Divisor K F) := by
    rw [hEeq, map_add, map_nsmul, hΨD₀, add_zero, nsmul_eq_mul]
    push_cast
    ring
  rw [hΨE] at hkey
  split_ifs at hkey with hc <;> omega

theorem eq_of_forall_mem [HasPrincipalDivisors K F]
    (hb : ∀ P ∈ S.dom, S.r₁ P ≠ S.r₂ P → S.r₁ P ∈ S.N₂ ∧ S.r₂ P ∈ S.N₁) :
    ∀ P ∈ S.dom, S.r₁ P = S.r₂ P := by
  classical
  intro P₀ hP₀
  by_contra hne
  obtain ⟨hX₀N₂, -⟩ := hb P₀ hP₀ hne
  set X₀ := S.r₁ P₀ with hX₀def
  have hX₀N₁ : X₀ ∉ S.N₁ := S.not_mem₁ P₀ hP₀
  set S₁ : Finset (Place k Fb) := S.N₂ \ S.N₁ with hS₁def
  set S₂ : Finset (Place k Fb) := S.N₁ \ S.N₂ with hS₂def
  have hX₀S₁ : X₀ ∈ S₁ := Finset.mem_sdiff.2 ⟨hX₀N₂, hX₀N₁⟩
  have hX₀S₂ : X₀ ∉ S₂ := fun h => hX₀N₁ (Finset.mem_sdiff.1 h).1

  obtain ⟨g, hg0, hg⟩ :=
    Place.exists_forall_ord_eq_finset (S₁ ∪ S₂) (fun v => if v = X₀ then (1 : ℤ) else 0)
  obtain ⟨f, hfg⟩ := S.lift g hg0
  obtain ⟨hf0, -⟩ := S.good_ne f g hfg
  obtain ⟨D, hD, hD'⟩ := S.exists_divisor hf0

  have hfib : ∀ (r : Place K F → Place k Fb) (T : Finset (Place k Fb)),
      (∀ Q ∈ T, Finsupp.mapDomain r D Q = Q.ord g) →
      ∑ Q ∈ T, Q.ord g = ∑ a ∈ D.support with r a ∈ T, D a := by
    intro r T hT
    calc ∑ Q ∈ T, Q.ord g = ∑ Q ∈ T, Finsupp.mapDomain r D Q := Finset.sum_congr rfl fun Q hQ => (hT Q hQ).symm
      _ = ∑ Q ∈ T, ∑ a ∈ D.support with r a = Q, D a :=
          Finset.sum_congr rfl fun Q _ => mapDomain_apply_eq_sum r D Q
      _ = ∑ Q ∈ T, ∑ a ∈ (D.support.filter (r · ∈ T)) with r a = Q, D a := by
          refine Finset.sum_congr rfl fun Q hQ => Finset.sum_congr ?_ fun _ _ => rfl
          ext a
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨ha, rfl⟩; exact ⟨⟨ha, hQ⟩, rfl⟩
          · rintro ⟨⟨ha, -⟩, h⟩; exact ⟨ha, h⟩
      _ = ∑ a ∈ D.support.filter (r · ∈ T), D a :=
          Finset.sum_fiberwise_of_maps_to (fun a ha => (Finset.mem_filter.1 ha).2) _
  have h₁ : ∑ Q ∈ S₁, Q.ord g = ∑ a ∈ D.support with S.r₁ a ∈ S₁, D a :=
    hfib S.r₁ S₁ fun Q hQ => S.law₁ f g hfg D hD hD' Q (Finset.mem_sdiff.1 hQ).2
  have h₂ : ∑ Q ∈ S₂, Q.ord g = ∑ a ∈ D.support with S.r₂ a ∈ S₂, D a :=
    hfib S.r₂ S₂ fun Q hQ => S.law₂ f g hfg D hD hD' Q (Finset.mem_sdiff.1 hQ).2

  have hsupp : D.support.filter (S.r₁ · ∈ S₁) = D.support.filter (S.r₂ · ∈ S₂) := by
    ext a
    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
    refine ⟨fun ⟨ha, h⟩ => ⟨ha, ?_⟩, fun ⟨ha, h⟩ => ⟨ha, ?_⟩⟩
    · have hadom : a ∈ S.dom := by
        by_contra hna
        exact ha (hD' a hna)
      have hne' : S.r₁ a ≠ S.r₂ a := fun heq => S.not_mem₂ a hadom (heq ▸ (Finset.mem_sdiff.1 h).1)
      exact Finset.mem_sdiff.2 ⟨(hb a hadom hne').2, S.not_mem₂ a hadom⟩
    · have hadom : a ∈ S.dom := by
        by_contra hna
        exact ha (hD' a hna)
      have hne' : S.r₁ a ≠ S.r₂ a := fun heq => S.not_mem₁ a hadom (heq.symm ▸ (Finset.mem_sdiff.1 h).1)
      exact Finset.mem_sdiff.2 ⟨(hb a hadom hne').1, S.not_mem₁ a hadom⟩
  have hsum : ∑ Q ∈ S₁, Q.ord g = ∑ Q ∈ S₂, Q.ord g := by rw [h₁, h₂, hsupp]

  have hL : ∑ Q ∈ S₁, Q.ord g = 1 := by
    rw [Finset.sum_congr rfl fun Q hQ => hg Q (Finset.mem_union_left _ hQ)]
    rw [Finset.sum_ite_eq' S₁ X₀ (fun _ => (1 : ℤ)), if_pos hX₀S₁]
  have hR : ∑ Q ∈ S₂, Q.ord g = 0 := by
    rw [Finset.sum_congr rfl fun Q hQ => hg Q (Finset.mem_union_right _ hQ)]
    rw [Finset.sum_ite_eq' S₂ X₀ (fun _ => (1 : ℤ)), if_neg hX₀S₂]
  rw [hL, hR] at hsum
  exact one_ne_zero hsum

theorem r₁_eq_r₂ [HasPrincipalDivisors K F] [Infinite (Place k Fb)]
    (hdeg : ∀ P : Place K F, P.deg = 1) (hdiv : ∀ y : Pic0 K F, ∃ z : Pic0 K F, 3 • z = y) :
    ∀ P ∈ S.dom, S.r₁ P = S.r₂ P :=
  S.eq_of_forall_mem fun P hP hne =>
    ⟨S.mem_of_ne hdeg hdiv P hP hne, S.swap.mem_of_ne hdeg hdiv P hP (Ne.symm hne)⟩

end Setup

end Core

section Theta

variable {L : Type} [Field L] {A : ValuationSubring L} {F : Type} [Field F] [Algebra L F]
  {Fbar Fbar' : Type} [Field Fbar] [Algebra (ResidueField A) Fbar] [Field Fbar'] [Algebra (ResidueField A) Fbar']
  (C : ComponentChart A F Fbar) (C' : ComponentChart A F Fbar') (g : SemilinearAut L F)
  (hint : ∀ f : F, f ∈ C.integers ↔ g • f ∈ C'.integers)

def gInt : C.integers ≃+* C'.integers where
  toFun x := ⟨g • (x : F), (hint x).1 x.2⟩
  invFun y := ⟨g⁻¹ • (y : F), (hint _).2 (by rw [smul_inv_smul]; exact y.2)⟩
  left_inv x := Subtype.ext (inv_smul_smul g (x : F))
  right_inv y := Subtype.ext (smul_inv_smul g (y : F))
  map_mul' x y := Subtype.ext (smul_mul' g (x : F) y)
  map_add' x y := Subtype.ext (smul_add g (x : F) y)

@[scoped simp] theorem coe_gInt (x : C.integers) : ((gInt C C' g hint x : C'.integers) : F) = g • (x : F) := rfl

def residue' : C.integers →+* Fbar' := C'.residue.comp (gInt C C' g hint).toRingHom

theorem residue'_apply (f : F) (h : f ∈ C.integers) (h' : g • f ∈ C'.integers) :
    residue' C C' g hint ⟨f, h⟩ = C'.residue ⟨g • f, h'⟩ := rfl

theorem residue'_surjective : Function.Surjective (residue' C C' g hint) :=
  C'.residue_surjective.comp (gInt C C' g hint).surjective

theorem mem_maximalIdeal_iff (x : C.integers) :
    gInt C C' g hint x ∈ maximalIdeal C'.integers ↔ x ∈ maximalIdeal C.integers := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  constructor
  · intro h
    have := h.map (gInt C C' g hint).symm
    rwa [RingEquiv.symm_apply_apply] at this
  · intro h
    exact h.map (gInt C C' g hint)

theorem ker_residue' : RingHom.ker (residue' C C' g hint) = maximalIdeal C.integers := by
  ext x
  rw [RingHom.mem_ker, residue', RingHom.comp_apply, ← RingHom.mem_ker, C'.ker_residue]
  exact mem_maximalIdeal_iff C C' g hint x

theorem ker_le₁ : RingHom.ker C.residue ≤ RingHom.ker (residue' C C' g hint) := by
  rw [C.ker_residue, ker_residue']

theorem ker_le₂ : RingHom.ker (residue' C C' g hint) ≤ RingHom.ker C.residue := by
  rw [C.ker_residue, ker_residue']

def thetaHom : Fbar →+* Fbar' :=
  C.residue.liftOfSurjective C.residue_surjective ⟨residue' C C' g hint, ker_le₁ C C' g hint⟩

def thetaInv : Fbar' →+* Fbar :=
  (residue' C C' g hint).liftOfSurjective (residue'_surjective C C' g hint) ⟨C.residue, ker_le₂ C C' g hint⟩

theorem thetaHom_residue (x : C.integers) : thetaHom C C' g hint (C.residue x) = residue' C C' g hint x :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

theorem thetaInv_residue' (x : C.integers) : thetaInv C C' g hint (residue' C C' g hint x) = C.residue x :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

def theta : Fbar ≃+* Fbar' := by
  refine RingEquiv.ofRingHom (thetaHom C C' g hint) (thetaInv C C' g hint) ?_ ?_
  · apply (RingHom.cancel_right (residue'_surjective C C' g hint)).1
    ext x
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [thetaInv_residue', thetaHom_residue]
  · apply (RingHom.cancel_right C.residue_surjective).1
    ext x
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [thetaHom_residue, thetaInv_residue']

theorem theta_residue (f : F) (h : f ∈ C.integers) (h' : g • f ∈ C'.integers) :
    C'.residue ⟨g • f, h'⟩ = theta C C' g hint (C.residue ⟨f, h⟩) := by
  show _ = thetaHom C C' g hint (C.residue ⟨f, h⟩)
  rw [thetaHom_residue]
  rfl

theorem theta_algebraMap (a : A) (h : SemilinearAut.baseAut g (a : L) ∈ A) :
    theta C C' g hint (algebraMap (ResidueField A) Fbar (residue A a)) =
      algebraMap (ResidueField A) Fbar' (residue A ⟨SemilinearAut.baseAut g (a : L), h⟩) := by
  have h1 : g • algebraMap L F (a : L) ∈ C'.integers :=
    (hint _).1 ((C.algebraMap_mem_iff (a : L)).mpr a.2)
  rw [← C.residue_algebraMap a, ← theta_residue C C' g hint _ _ h1, ← C'.residue_algebraMap ⟨_, h⟩]
  congr 1
  exact Subtype.ext (SemilinearAut.smul_algebraMap g (a : L))

end Theta

section PlaceTransport

variable {k Fb Fb' : Type} [Field k] [Field Fb] [Algebra k Fb] [Field Fb'] [Algebra k Fb']

def vsub (θ : Fb ≃+* Fb') (v : Place k Fb) : ValuationSubring Fb' :=
  ValuationSubring.comap v.toValuationSubring θ.symm.toRingHom

theorem mem_vsub_iff (θ : Fb ≃+* Fb') (v : Place k Fb) (y : Fb') :
    y ∈ vsub θ v ↔ θ.symm y ∈ v.toValuationSubring := Iff.rfl

def vsubEquiv (θ : Fb ≃+* Fb') (v : Place k Fb) : v.toValuationSubring ≃+* vsub θ v where
  toFun x := ⟨θ x, by rw [mem_vsub_iff, RingEquiv.symm_apply_apply]; exact x.2⟩
  invFun y := ⟨θ.symm y, (mem_vsub_iff θ v y).1 y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul θ _ _)
  map_add' x y := Subtype.ext (map_add θ _ _)

@[scoped simp] theorem coe_vsubEquiv (θ : Fb ≃+* Fb') (v : Place k Fb) (x : v.toValuationSubring) :
    ((vsubEquiv θ v x : vsub θ v) : Fb') = θ (x : Fb) := rfl

def placeMapEquiv (θ : Fb ≃+* Fb') (hθ : ∀ a : k, ∃ b : k, θ (algebraMap k Fb b) = algebraMap k Fb' a)
    (v : Place k Fb) : Place k Fb' where
  toValuationSubring := vsub θ v
  algebraMap_mem' a := by
    obtain ⟨b, hb⟩ := hθ a
    rw [mem_vsub_iff, ← hb, RingEquiv.symm_apply_apply]
    exact v.algebraMap_mem' b
  ne_top' h := v.ne_top' (by
    ext x
    refine ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
    have hx : θ x ∈ vsub θ v := h.symm ▸ ValuationSubring.mem_top _
    rw [mem_vsub_iff, RingEquiv.symm_apply_apply] at hx
    exact hx)
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective (vsubEquiv θ v).toRingHom (vsubEquiv θ v).surjective

theorem mem_placeMapEquiv_iff (θ : Fb ≃+* Fb') (hθ : ∀ a : k, ∃ b : k, θ (algebraMap k Fb b) = algebraMap k Fb' a)
    (v : Place k Fb) (y : Fb') : y ∈ (placeMapEquiv θ hθ v).toValuationSubring ↔ θ.symm y ∈ v.toValuationSubring :=
  Iff.rfl

theorem ord_placeMapEquiv (θ : Fb ≃+* Fb') (hθ : ∀ a : k, ∃ b : k, θ (algebraMap k Fb b) = algebraMap k Fb' a)
    (v : Place k Fb) (f : Fb) : (placeMapEquiv θ hθ v).ord (θ f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  set n := v.ord f with hn
  let e : v.toValuationSubring ≃+* (placeMapEquiv θ hθ v).toValuationSubring := vsubEquiv θ v
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hu' : IsUnit (e (u : v.toValuationSubring)) := u.isUnit.map e
  have hcoeu : ((hu'.unit : (placeMapEquiv θ hθ v).toValuationSubring) : Fb') = θ ((u : v.toValuationSubring) : Fb) := by
    rw [IsUnit.unit_spec]; rfl
  have hcoeπ : ((e π : (placeMapEquiv θ hθ v).toValuationSubring) : Fb') = θ (π : Fb) := rfl
  have key : θ f = ((hu'.unit : (placeMapEquiv θ hθ v).toValuationSubring) : Fb') *
      (((e π : (placeMapEquiv θ hθ v).toValuationSubring) : Fb') ^ n) := by
    rw [hcoeu, hcoeπ, hu, map_mul, map_zpow₀]
  rw [key, (placeMapEquiv θ hθ v).ord_unit_smul_zpow hu'.unit hπ' n]

theorem placeMapEquiv_symm_apply (θ : Fb ≃+* Fb')
    (hθ : ∀ a : k, ∃ b : k, θ (algebraMap k Fb b) = algebraMap k Fb' a)
    (hθ' : ∀ b : k, ∃ a : k, θ.symm (algebraMap k Fb' a) = algebraMap k Fb b) (v : Place k Fb) :
    placeMapEquiv θ.symm hθ' (placeMapEquiv θ hθ v) = v := by
  apply Place.ext
  ext x
  rw [mem_placeMapEquiv_iff, mem_placeMapEquiv_iff]
  simp

theorem placeMapEquiv_apply_symm (θ : Fb ≃+* Fb')
    (hθ : ∀ a : k, ∃ b : k, θ (algebraMap k Fb b) = algebraMap k Fb' a)
    (hθ' : ∀ b : k, ∃ a : k, θ.symm (algebraMap k Fb' a) = algebraMap k Fb b) (w : Place k Fb') :
    placeMapEquiv θ hθ (placeMapEquiv θ.symm hθ' w) = w := by
  apply Place.ext
  ext x
  rw [mem_placeMapEquiv_iff, mem_placeMapEquiv_iff]
  simp

def placeEquiv (θ : Fb ≃+* Fb')
    (hθ : ∀ a : k, ∃ b : k, θ (algebraMap k Fb b) = algebraMap k Fb' a)
    (hθ' : ∀ b : k, ∃ a : k, θ.symm (algebraMap k Fb' a) = algebraMap k Fb b) :
    Place k Fb ≃ Place k Fb' where
  toFun := placeMapEquiv θ hθ
  invFun := placeMapEquiv θ.symm hθ'
  left_inv := placeMapEquiv_symm_apply θ hθ hθ'
  right_inv := placeMapEquiv_apply_symm θ hθ hθ'

@[scoped simp] theorem placeEquiv_apply (θ : Fb ≃+* Fb')
    (hθ : ∀ a : k, ∃ b : k, θ (algebraMap k Fb b) = algebraMap k Fb' a)
    (hθ' : ∀ b : k, ∃ a : k, θ.symm (algebraMap k Fb' a) = algebraMap k Fb b) (v : Place k Fb) :
    placeEquiv θ hθ hθ' v = placeMapEquiv θ hθ v := rfl

end PlaceTransport

end PMT
p2m_reactivate "P2MW.S_AlgebraicCurve_ComponentChart_exists_equiv_placeMap_smul_eq_of_forall_mem_integers_iff_of_forall_mem_dom_iff_of_discFibres.PMT"

namespace PMT

open scoped Classical

section Main

theorem main
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (F : Type) [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar Fbar' : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar'] [IsCurveOver (ResidueField A) Fbar']
    (C : ComponentChart A F Fbar) (C' : ComponentChart A F Fbar')
    (hsurjC : ∀ Q, Q ∉ C.nodes → ∃ P ∈ C.dom, C.placeMap P = Q)
    (hsurjC' : ∀ Q, Q ∉ C'.nodes → ∃ P ∈ C'.dom, C'.placeMap P = Q)
    (g : SemilinearAut L F) (hA : ∀ a : L, a ∈ A ↔ SemilinearAut.baseAut g a ∈ A)
    (hint : ∀ f : F, f ∈ C.integers ↔ g • f ∈ C'.integers)
    (hdomg : ∀ P : Place L F, P ∈ C.dom ↔ g • P ∈ C'.dom) :
    ∃ (θ : Fbar ≃+* Fbar') (Θ : Place (ResidueField A) Fbar ≃ Place (ResidueField A) Fbar'),
      (∀ (f : F) (hf : f ∈ C.integers) (hf' : g • f ∈ C'.integers), C'.residue ⟨g • f, hf'⟩ = θ (C.residue ⟨f, hf⟩)) ∧
      (∀ (Q : Place (ResidueField A) Fbar) (φ : Fbar), (Θ Q).ord (θ φ) = Q.ord φ) ∧
      (∀ Q, Q ∈ C.nodes ↔ Θ Q ∈ C'.nodes) ∧
      ∀ P ∈ C.dom, C'.placeMap (g • P) = Θ (C.placeMap P) := by
  classical
  set θ := theta C C' g hint with hθdef
  have hθ : ∀ (f : F) (hf : f ∈ C.integers) (hf' : g • f ∈ C'.integers),
      C'.residue ⟨g • f, hf'⟩ = θ (C.residue ⟨f, hf⟩) := theta_residue C C' g hint

  have hθκ : ∀ a : ResidueField A, ∃ b : ResidueField A,
      θ (algebraMap (ResidueField A) Fbar b) = algebraMap (ResidueField A) Fbar' a := by
    intro a
    obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
    set σ := SemilinearAut.baseAut g with hσ
    have hb₀ : σ.symm (a₀ : L) ∈ A := by
      have := (hA (σ.symm (a₀ : L))).not
      by_contra hc
      exact (this.1 hc) (by rw [RingEquiv.apply_symm_apply]; exact a₀.2)
    refine ⟨residue A ⟨σ.symm (a₀ : L), hb₀⟩, ?_⟩
    have h2 : σ ((⟨σ.symm (a₀ : L), hb₀⟩ : A) : L) ∈ A := by
      rw [RingEquiv.apply_symm_apply]; exact a₀.2
    rw [theta_algebraMap C C' g hint ⟨σ.symm (a₀ : L), hb₀⟩ h2]
    congr 2
    exact Subtype.ext (RingEquiv.apply_symm_apply σ (a₀ : L))
  have hθκ' : ∀ b : ResidueField A, ∃ a : ResidueField A,
      θ.symm (algebraMap (ResidueField A) Fbar' a) = algebraMap (ResidueField A) Fbar b := by
    intro b
    obtain ⟨b₀, rfl⟩ := IsLocalRing.residue_surjective b
    have h2 : SemilinearAut.baseAut g (b₀ : L) ∈ A := (hA _).1 b₀.2
    refine ⟨residue A ⟨_, h2⟩, ?_⟩
    rw [← theta_algebraMap C C' g hint b₀ h2, RingEquiv.symm_apply_apply]
  set Θ : Place (ResidueField A) Fbar ≃ Place (ResidueField A) Fbar' := placeEquiv θ hθκ hθκ' with hΘdef
  have hΘord : ∀ (Q : Place (ResidueField A) Fbar) (φ : Fbar), (Θ Q).ord (θ φ) = Q.ord φ :=
    fun Q φ => ord_placeMapEquiv θ hθκ Q φ

  have hmain : ∀ P ∈ C.dom, C'.placeMap (g • P) = Θ (C.placeMap P) := by

    haveI : PerfectField L := IsAlgClosed.perfectField L
    obtain ⟨x, hx, hfd, -⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := L) (F := F)
    have hdeg : ∀ P : Place L F, P.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
    have hdiv : ∀ y : Pic0 L F, ∃ z, 3 • z = y := fun y =>
      AlgebraicCurve.Pic0.exists_nsmul_eq L F ⟨x, hx, hfd⟩ 3 (by norm_num) y
    haveI : HasPrincipalDivisors L F := IsCurveOver.hasPrincipalDivisors
    let S : Setup L F (ResidueField A) Fbar' :=
      { dom := C.dom
        good := fun f g' => ∃ hf : f ∈ C.integers, θ (C.residue ⟨f, hf⟩) = g' ∧ g' ≠ 0
        r₁ := fun P => Θ (C.placeMap P)
        r₂ := fun P => C'.placeMap (g • P)
        N₁ := C.nodes.image Θ
        N₂ := C'.nodes
        good_ne := by
          rintro f g' ⟨hf, hfg, hg⟩
          refine ⟨?_, hg⟩
          rintro rfl
          apply hg
          rw [← hfg]
          have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
          rw [this, map_zero, map_zero]
        law₁ := by
          rintro f g' ⟨hf, hfg, hg⟩ D hD hD' Q' hQ'
          have hres : C.residue ⟨f, hf⟩ ≠ 0 := by
            intro h0; apply hg; rw [← hfg, h0, map_zero]
          set Q := Θ.symm Q' with hQdef
          have hQQ' : Θ Q = Q' := Θ.apply_symm_apply Q'
          have hQ : Q ∉ C.nodes := fun h => hQ' (Finset.mem_image.2 ⟨Q, h, hQQ'⟩)
          have hcomp : (fun P => Θ (C.placeMap P)) = Θ ∘ C.placeMap := rfl
          rw [hcomp, Finsupp.mapDomain_comp, ← hQQ', Finsupp.mapDomain_apply Θ.injective,
            C.mapDomain_placeMap ⟨f, hf⟩ hres D hD hD' Q hQ, ← hfg]
          exact (hΘord Q _).symm
        law₂ := by
          rintro f g' ⟨hf, hfg, hg⟩ D hD hD' Q' hQ'
          have hf' : g • f ∈ C'.integers := (hint f).1 hf
          have hres' : C'.residue ⟨g • f, hf'⟩ ≠ 0 := by rw [hθ f hf hf', hfg]; exact hg
          have hcomp : (fun P => C'.placeMap (g • P)) = C'.placeMap ∘ (fun P => g • P) := rfl
          rw [hcomp, Finsupp.mapDomain_comp, ← SemilinearAut.divisor_smul_def]
          rw [C'.mapDomain_placeMap ⟨g • f, hf'⟩ hres' (g • D) ?_ ?_ Q' hQ', hθ f hf hf', hfg]
          · intro P' hP'
            rw [SemilinearAut.divisor_smul_apply]
            have hPd : g⁻¹ • P' ∈ C.dom := (hdomg _).2 (by rw [smul_inv_smul]; exact hP')
            rw [hD _ hPd]
            have := SemilinearAut.ord_smul g (g⁻¹ • P') f
            rw [smul_inv_smul] at this
            exact this.symm
          · intro P' hP'
            rw [SemilinearAut.divisor_smul_apply]
            exact hD' _ (fun h => hP' (by have := (hdomg _).1 h; rwa [smul_inv_smul] at this))
        lift := by
          intro g' hg'
          obtain ⟨⟨f, hf⟩, hfg⟩ := C.residue_surjective (θ.symm g')
          exact ⟨f, hf, by rw [hfg, RingEquiv.apply_symm_apply], hg'⟩
        scale := by
          intro h hh
          obtain ⟨c, hc, hres⟩ := C.exists_smul_mem h hh
          have hc0 : c ≠ 0 := by
            rintro rfl
            apply hres
            have : (⟨(0 : L) • h, hc⟩ : C.integers) = 0 := Subtype.ext (zero_smul L h)
            rw [this, map_zero]
          exact ⟨c • h, θ (C.residue ⟨c • h, hc⟩), ⟨hc, rfl, (map_ne_zero θ).2 hres⟩, fun v => ord_smul v c hc0 h hh⟩
        not_mem₁ := by
          intro P hP h
          obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.1 h
          have : Q = C.placeMap P := Θ.injective hQeq
          exact C.placeMap_not_mem_nodes P hP (this ▸ hQ)
        not_mem₂ := fun P hP => C'.placeMap_not_mem_nodes (g • P) ((hdomg P).1 hP)
        surj₁ := by
          intro Q' hQ'
          have hQ : Θ.symm Q' ∉ C.nodes := fun h =>
            hQ' (Finset.mem_image.2 ⟨Θ.symm Q', h, Θ.apply_symm_apply Q'⟩)
          obtain ⟨P, hP, hPQ⟩ := hsurjC _ hQ
          exact ⟨P, hP, by simp only [hPQ, Equiv.apply_symm_apply]⟩
        surj₂ := by
          intro Q' hQ'
          obtain ⟨P', hP', hPQ⟩ := hsurjC' Q' hQ'
          refine ⟨g⁻¹ • P', (hdomg _).2 (by rw [smul_inv_smul]; exact hP'), ?_⟩
          simp only [smul_inv_smul, hPQ] }
    intro P hP
    haveI : Infinite (Place (ResidueField A) Fbar') := infinite_place (C'.placeMap (g • P))
    have h := S.r₁_eq_r₂ hdeg hdiv P hP
    exact h.symm
  refine ⟨θ, Θ, hθ, hΘord, fun Q => ?_, hmain⟩

  rw [← not_iff_not]
  constructor
  · intro hQ hQ'
    obtain ⟨P, hP, hPQ⟩ := hsurjC Q hQ
    have h := C'.placeMap_not_mem_nodes (g • P) ((hdomg P).1 hP)
    rw [hmain P hP, hPQ] at h
    exact h hQ'
  · intro hQ' hQ
    obtain ⟨P', hP', hPQ⟩ := hsurjC' (Θ Q) hQ'
    have hPd : g⁻¹ • P' ∈ C.dom := (hdomg _).2 (by rw [smul_inv_smul]; exact hP')
    have h := hmain _ hPd
    rw [smul_inv_smul, hPQ] at h
    have : C.placeMap (g⁻¹ • P') = Q := (Θ.injective h).symm
    exact C.placeMap_not_mem_nodes _ hPd (this ▸ hQ)

end Main
p2m_reactivate "P2MW.S_AlgebraicCurve_ComponentChart_exists_equiv_placeMap_smul_eq_of_forall_mem_integers_iff_of_forall_mem_dom_iff_of_discFibres.PMT"

end PMT
p2m_reactivate "P2MW.S_AlgebraicCurve_ComponentChart_exists_equiv_placeMap_smul_eq_of_forall_mem_integers_iff_of_forall_mem_dom_iff_of_discFibres.PMT"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_ComponentChart_exists_equiv_placeMap_smul_eq_of_forall_mem_integers_iff_of_forall_mem_dom_iff_of_discFibres.PMT"

open AlgebraicCurve IsLocalRing in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar Fbar' : Type} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [Field Fbar'] [Algebra (IsLocalRing.ResidueField A) Fbar']
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar] [Algebra.EssFiniteType (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar'] [Algebra.EssFiniteType (IsLocalRing.ResidueField A) Fbar']
    (hratBar : ∀ Q : Place (IsLocalRing.ResidueField A) Fbar, Q.IsRational)
    (hratBar' : ∀ Q : Place (IsLocalRing.ResidueField A) Fbar', Q.IsRational)
    (C : ComponentChart A F Fbar) (C' : ComponentChart A F Fbar')
    (hratF : ∀ P ∈ C.dom, P.IsRational) (hratF' : ∀ P ∈ C'.dom, P.IsRational)
    (hdisc :
      (∀ Q : Place (IsLocalRing.ResidueField A) Fbar, Q ∉ C.nodes →
        ∃ (T : F) (hT : T ∈ C.integers), C.residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord (C.residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ C.dom, C.placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place L F, P ∈ C.dom ∧ C.placeMap P = Q ∧ P.evalAt T = c))
    (hdisc' :
      (∀ Q : Place (IsLocalRing.ResidueField A) Fbar', Q ∉ C'.nodes →
        ∃ (T : F) (hT : T ∈ C'.integers), C'.residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord (C'.residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ C'.dom, C'.placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place L F, P ∈ C'.dom ∧ C'.placeMap P = Q ∧ P.evalAt T = c))
    (g : SemilinearAut L F) (hA : ∀ a : L, a ∈ A ↔ SemilinearAut.baseAut g a ∈ A)
    (hint : ∀ f : F, f ∈ C.integers ↔ g • f ∈ C'.integers)
    (hdomg : ∀ P : Place L F, P ∈ C.dom ↔ g • P ∈ C'.dom) :
    ∃ (θ : Fbar ≃+* Fbar') (Θ : Place (IsLocalRing.ResidueField A) Fbar ≃ Place (IsLocalRing.ResidueField A) Fbar'),
      (∀ (f : F) (hf : f ∈ C.integers) (hf' : g • f ∈ C'.integers), C'.residue ⟨g • f, hf'⟩ = θ (C.residue ⟨f, hf⟩)) ∧
      (∀ (Q : Place (IsLocalRing.ResidueField A) Fbar) (φ : Fbar), (Θ Q).ord (θ φ) = Q.ord φ) ∧
      (∀ Q, Q ∈ C.nodes ↔ Θ Q ∈ C'.nodes) ∧
      ∀ P ∈ C.dom, C'.placeMap (g • P) = Θ (C.placeMap P) := by
  have hsurjC : ∀ Q, Q ∉ C.nodes → ∃ P ∈ C.dom, C.placeMap P = Q := by
    intro Q hQ
    obtain ⟨T, hT, -, -, -, hd⟩ := hdisc Q hQ
    obtain ⟨P, ⟨hP, hPQ, -⟩, -⟩ := hd 0 (Ideal.zero_mem _)
    exact ⟨P, hP, hPQ⟩
  have hsurjC' : ∀ Q, Q ∉ C'.nodes → ∃ P ∈ C'.dom, C'.placeMap P = Q := by
    intro Q hQ
    obtain ⟨T, hT, -, -, -, hd⟩ := hdisc' Q hQ
    obtain ⟨P, ⟨hP, hPQ, -⟩, -⟩ := hd 0 (Ideal.zero_mem _)
    exact ⟨P, hP, hPQ⟩
  exact PMT.main A F C C' hsurjC hsurjC' g hA hint hdomg

end S_AlgebraicCurve_ComponentChart_exists_equiv_placeMap_smul_eq_of_forall_mem_integers_iff_of_forall_mem_dom_iff_of_discFibres
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_exists_equiv_placeMap_smul_eq_of_forall_mem_integers_iff_of_forall_mem_dom_iff_of_discFibres (solution)
