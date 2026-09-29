-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.exists_algEquiv_residue_eq_and_placeMap_eq_smul_of_integers_eq_of_dom_eq_of_hasDiscFibres
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/764869c6-8466-5b81-b316-3caea22ba840

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_exists_algEquiv_residue_eq_and_placeMap_eq_smul_of_integers_eq_of_dom_eq_of_hasDiscFibres
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

noncomputable section

namespace KcPlaceMapUniq

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap (v : Place K F) (c : K) (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  let u : v.toValuationSubringˣ :=
    ⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  exact v.ord_coe_unit u

private theorem _root_.KcPlaceMapUniq.ord_smul (v : Place K F) (c : K) (hc : c ≠ 0) (f : F) (hf : f ≠ 0) :
    v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).2 hc) hf, ord_algebraMap v c hc, zero_add]

p2m_export "KcPlaceMapUniq" "ord_smul"

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

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def inclEquiv (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) : C.integers ≃+* C'.integers where
  toFun x := ⟨x.1, by rw [hO]; exact x.2⟩
  invFun x := ⟨x.1, by rw [← hO]; exact x.2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl

@[scoped simp] theorem coe_inclEquiv (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) (x : C.integers) :
    ((inclEquiv C C' hO x : C'.integers) : F) = x := rfl

def residue' (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) : C.integers →+* Fbar :=
  C'.residue.comp (inclEquiv C C' hO).toRingHom

theorem residue'_apply (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) (f : F)
    (h : f ∈ C.integers) (h' : f ∈ C'.integers) : residue' C C' hO ⟨f, h⟩ = C'.residue ⟨f, h'⟩ := rfl

theorem residue'_surjective (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) :
    Function.Surjective (residue' C C' hO) :=
  C'.residue_surjective.comp (inclEquiv C C' hO).surjective

theorem mem_maximalIdeal_iff (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) (x : C.integers) :
    inclEquiv C C' hO x ∈ maximalIdeal C'.integers ↔ x ∈ maximalIdeal C.integers := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  constructor
  · intro h
    have := h.map (inclEquiv C C' hO).symm
    rwa [RingEquiv.symm_apply_apply] at this
  · intro h
    exact h.map (inclEquiv C C' hO)

theorem ker_residue' (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) :
    RingHom.ker (residue' C C' hO) = maximalIdeal C.integers := by
  ext x
  rw [RingHom.mem_ker, residue', RingHom.comp_apply, ← RingHom.mem_ker, C'.ker_residue]
  exact mem_maximalIdeal_iff C C' hO x

theorem ker_le₁ (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) :
    RingHom.ker C.residue ≤ RingHom.ker (residue' C C' hO) := by
  rw [C.ker_residue, ker_residue']

theorem ker_le₂ (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) :
    RingHom.ker (residue' C C' hO) ≤ RingHom.ker C.residue := by
  rw [C.ker_residue, ker_residue']

def thetaHom (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) : Fbar →+* Fbar :=
  C.residue.liftOfSurjective C.residue_surjective ⟨residue' C C' hO, ker_le₁ C C' hO⟩

def thetaInv (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) : Fbar →+* Fbar :=
  (residue' C C' hO).liftOfSurjective (residue'_surjective C C' hO) ⟨C.residue, ker_le₂ C C' hO⟩

theorem thetaHom_residue (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) (x : C.integers) :
    thetaHom C C' hO (C.residue x) = residue' C C' hO x :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

theorem thetaInv_residue' (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) (x : C.integers) :
    thetaInv C C' hO (residue' C C' hO x) = C.residue x :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

def thetaRingEquiv (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) : Fbar ≃+* Fbar := by
  refine RingEquiv.ofRingHom (thetaHom C C' hO) (thetaInv C C' hO) ?_ ?_
  · apply (RingHom.cancel_right (residue'_surjective C C' hO)).1
    ext x
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [thetaInv_residue', thetaHom_residue]
  · apply (RingHom.cancel_right C.residue_surjective).1
    ext x
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [thetaHom_residue, thetaInv_residue']

theorem thetaRingEquiv_residue (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) (x : C.integers) :
    thetaRingEquiv C C' hO (C.residue x) = residue' C C' hO x :=
  thetaHom_residue C C' hO x

def theta (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) : Fbar ≃ₐ[ResidueField A] Fbar :=
  AlgEquiv.ofRingEquiv (f := thetaRingEquiv C C' hO) (by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← C.residue_algebraMap a, thetaRingEquiv_residue, residue'_apply _ _ _ _ _
      ((C'.algebraMap_mem_iff a).mpr a.2), C'.residue_algebraMap]
    exact (C.residue_algebraMap a).symm)

theorem theta_residue (C C' : ComponentChart A F Fbar) (hO : C'.integers = C.integers) (f : F)
    (h : f ∈ C.integers) (h' : f ∈ C'.integers) : C'.residue ⟨f, h'⟩ = theta C C' hO (C.residue ⟨f, h⟩) := by
  show _ = thetaRingEquiv C C' hO (C.residue ⟨f, h⟩)
  rw [thetaRingEquiv_residue]
  rfl

end Theta

section FieldFacts

open scoped MatrixGroups
open ModularCurve ModularCurve.FullLevel

theorem gamma1_le_gammaH (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    CongruenceSubgroup.Gamma1 N ≤ CohCarrier.GammaH N H := by
  intro γ hγ
  rw [CohCarrier.mem_GammaH_iff]
  obtain ⟨-, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem N γ).mp hγ
  refine ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_⟩
  have h1 : CohCarrier.gamma0Units N ⟨γ, CongruenceSubgroup.Gamma0_mem.mpr h10⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    simpa [CongruenceSubgroup.Gamma0Map] using h11
  rw [h1]
  exact one_mem H

theorem T_mem_gamma1 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T]

scoped instance finiteIndex_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) : (CohCarrier.GammaH N H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (gamma1_le_gammaH N H)

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

scoped instance neZero_sq_mul : NeZero (q ^ 2 * M') :=
  ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩

theorem exists_transcendental_fieldBar :
    ∃ x : ↥(fieldBar q M'), Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(fieldBar q M')))
        ↥(fieldBar q M') := by
  obtain ⟨x, hx, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))
    ((gamma1_le_gammaH _ _) (T_mem_gamma1 _))
  exact ⟨x, hx, hfd⟩

end FieldFacts

section Main

open ModularCurve ModularCurve.FullLevel

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem main
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [IsCurveOver (ResidueField A) Fbar] [Algebra.EssFiniteType (ResidueField A) Fbar]
    (C C' : ComponentChart A (fieldBar q M') Fbar)
    (hO : C'.integers = C.integers) (hdom : C'.dom = C.dom)
    (hC : SemistableCovering.HasDiscFibres C) (hC' : SemistableCovering.HasDiscFibres C') :
    ∃ θ : Fbar ≃ₐ[ResidueField A] Fbar,
      (∀ (f : fieldBar q M') (h : f ∈ C.integers) (h' : f ∈ C'.integers), C'.residue ⟨f, h'⟩ = θ (C.residue ⟨f, h⟩)) ∧
      (∀ Q : Place (ResidueField A) Fbar, SemilinearAut.ofAlgAut θ • Q ∈ C'.nodes ↔ Q ∈ C.nodes) ∧
      ∀ P ∈ C.dom, C'.placeMap P = SemilinearAut.ofAlgAut θ • C.placeMap P := by
  classical
  set θ := theta C C' hO with hθdef
  have hθ : ∀ (f : fieldBar q M') (h : f ∈ C.integers) (h' : f ∈ C'.integers),
      C'.residue ⟨f, h'⟩ = θ (C.residue ⟨f, h⟩) := theta_residue C C' hO
  set σ := SemilinearAut.ofAlgAut θ with hσdef

  have hsurjC : ∀ Q, Q ∉ C.nodes → ∃ P ∈ C.dom, C.placeMap P = Q := by
    intro Q hQ
    obtain ⟨T, hT, -, -, -, hdisc⟩ := hC Q hQ
    obtain ⟨P, ⟨hP, hPQ, -⟩, -⟩ := hdisc 0 (Ideal.zero_mem _)
    exact ⟨P, hP, hPQ⟩
  have hsurjC' : ∀ Q, Q ∉ C'.nodes → ∃ P ∈ C.dom, C'.placeMap P = Q := by
    intro Q hQ
    obtain ⟨T, hT, -, -, -, hdisc⟩ := hC' Q hQ
    obtain ⟨P, ⟨hP, hPQ, -⟩, -⟩ := hdisc 0 (Ideal.zero_mem _)
    exact ⟨P, hdom ▸ hP, hPQ⟩

  have hiii : ∀ P ∈ C.dom, C'.placeMap P = σ • C.placeMap P := by

    obtain ⟨x, hx, hfd⟩ := exists_transcendental_fieldBar q M'
    haveI := hfd
    haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(fieldBar q M') :=
      AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx
    have hdeg : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.deg = 1 :=
      IsCurveOver.deg_eq_one_of_isAlgClosed
    have hdiv : ∀ y : Pic0 (AlgebraicClosure ℚ) ↥(fieldBar q M'), ∃ z, 3 • z = y := fun y =>
      AlgebraicCurve.Pic0.exists_nsmul_eq (AlgebraicClosure ℚ) _ ⟨x, hx, hfd⟩ 3 (by norm_num) y

    let S : Setup (AlgebraicClosure ℚ) ↥(fieldBar q M') (ResidueField A) Fbar :=
      { dom := C.dom
        good := fun f g => ∃ hf : f ∈ C.integers, C.residue ⟨f, hf⟩ = g ∧ g ≠ 0
        r₁ := C.placeMap
        r₂ := fun P => σ⁻¹ • C'.placeMap P
        N₁ := C.nodes
        N₂ := C'.nodes.image (σ⁻¹ • ·)
        good_ne := by
          rintro f g ⟨hf, hfg, hg⟩
          refine ⟨fun h0 => hg ?_, hg⟩
          rw [← hfg]
          have : (⟨f, hf⟩ : C.integers) = 0 := Subtype.ext h0
          rw [this, map_zero]
        law₁ := by
          rintro f g ⟨hf, hfg, hg⟩ D hD hD' Q hQ
          have hres : C.residue ⟨f, hf⟩ ≠ 0 := by rwa [hfg]
          rw [C.mapDomain_placeMap ⟨f, hf⟩ hres D hD hD' Q hQ, hfg]
        law₂ := by
          rintro f g ⟨hf, hfg, hg⟩ D hD hD' Q hQ
          have hf' : f ∈ C'.integers := hO ▸ hf
          have hres' : C'.residue ⟨f, hf'⟩ ≠ 0 := by
            rw [hθ f hf hf', hfg]
            exact (map_ne_zero θ).2 hg
          have hQ' : σ • Q ∉ C'.nodes := by
            intro h
            exact hQ (Finset.mem_image.2 ⟨σ • Q, h, inv_smul_smul σ Q⟩)
          have hcomp : (fun P => σ⁻¹ • C'.placeMap P) = (fun Q' => σ⁻¹ • Q') ∘ C'.placeMap := rfl
          have hinj : Function.Injective (fun Q' : Place (ResidueField A) Fbar => σ⁻¹ • Q') :=
            MulAction.injective σ⁻¹
          rw [hcomp, Finsupp.mapDomain_comp]
          conv_lhs => rw [show Q = σ⁻¹ • (σ • Q) from (inv_smul_smul σ Q).symm]
          rw [Finsupp.mapDomain_apply hinj,
            C'.mapDomain_placeMap ⟨f, hf'⟩ hres' D (fun P hP => hD P (hdom ▸ hP))
              (fun P hP => hD' P (hdom ▸ hP)) (σ • Q) hQ',
            hθ f hf hf', hfg, ← SemilinearAut.ofAlgAut_smul θ g, SemilinearAut.ord_smul]
        lift := by
          intro g hg
          obtain ⟨⟨f, hf⟩, hfg⟩ := C.residue_surjective g
          exact ⟨f, hf, hfg, hg⟩
        scale := by
          intro h hh
          obtain ⟨c, hc, hres⟩ := C.exists_smul_mem h hh
          have hc0 : c ≠ 0 := by
            rintro rfl
            apply hres
            have : (⟨(0 : AlgebraicClosure ℚ) • h, hc⟩ : C.integers) = 0 := Subtype.ext (zero_smul (AlgebraicClosure ℚ) h)
            rw [this, map_zero]
          exact ⟨c • h, C.residue ⟨c • h, hc⟩, ⟨hc, rfl, hres⟩, fun v => ord_smul v c hc0 h hh⟩
        not_mem₁ := C.placeMap_not_mem_nodes
        not_mem₂ := by
          intro P hP h
          obtain ⟨Q', hQ', hQ'eq⟩ := Finset.mem_image.1 h
          have : Q' = C'.placeMap P := MulAction.injective σ⁻¹ hQ'eq
          exact C'.placeMap_not_mem_nodes P (hdom ▸ hP) (this ▸ hQ')
        surj₁ := hsurjC
        surj₂ := by
          intro Q hQ
          have hQ' : σ • Q ∉ C'.nodes := by
            intro h
            exact hQ (Finset.mem_image.2 ⟨σ • Q, h, inv_smul_smul σ Q⟩)
          obtain ⟨P, hP, hPQ⟩ := hsurjC' (σ • Q) hQ'
          exact ⟨P, hP, by simp only [hPQ, inv_smul_smul]⟩ }
    intro P hP
    haveI : Infinite (Place (ResidueField A) Fbar) := infinite_place (C.placeMap P)
    have h := S.r₁_eq_r₂ hdeg hdiv P hP

    change C.placeMap P = σ⁻¹ • C'.placeMap P at h
    rw [h, smul_inv_smul]
  refine ⟨θ, hθ, fun Q => ?_, hiii⟩

  rw [← not_iff_not]
  constructor
  · intro hQ'
    obtain ⟨P, hP, hPQ⟩ := hsurjC' (σ • Q) hQ'
    rw [hiii P hP] at hPQ
    have : C.placeMap P = Q := MulAction.injective σ hPQ
    exact this ▸ C.placeMap_not_mem_nodes P hP
  · intro hQ
    obtain ⟨P, hP, hPQ⟩ := hsurjC Q hQ
    have h := C'.placeMap_not_mem_nodes P (hdom ▸ hP)
    rwa [hiii P hP, hPQ] at h

end Main

end KcPlaceMapUniq
p2m_reactivate "P2MW.S_AlgebraicCurve_ComponentChart_exists_algEquiv_residue_eq_and_placeMap_eq_smul_of_integers_eq_of_dom_eq_of_hasDiscFibres.KcPlaceMapUniq"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_ComponentChart_exists_algEquiv_residue_eq_and_placeMap_eq_smul_of_integers_eq_of_dom_eq_of_hasDiscFibres.KcPlaceMapUniq"

open ModularCurve ModularCurve.FullLevel AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [IsCurveOver (ResidueField A) Fbar] [Algebra.EssFiniteType (ResidueField A) Fbar]
    (C C' : ComponentChart A (fieldBar q M') Fbar)
    (hO : C'.integers = C.integers) (hdom : C'.dom = C.dom)
    (hC : SemistableCovering.HasDiscFibres C) (hC' : SemistableCovering.HasDiscFibres C') :
    ∃ θ : Fbar ≃ₐ[ResidueField A] Fbar,
      (∀ (f : fieldBar q M') (h : f ∈ C.integers) (h' : f ∈ C'.integers), C'.residue ⟨f, h'⟩ = θ (C.residue ⟨f, h⟩)) ∧
      (∀ Q : Place (ResidueField A) Fbar, SemilinearAut.ofAlgAut θ • Q ∈ C'.nodes ↔ Q ∈ C.nodes) ∧
      ∀ P ∈ C.dom, C'.placeMap P = SemilinearAut.ofAlgAut θ • C.placeMap P :=
  KcPlaceMapUniq.main C C' hO hdom hC hC'

end S_AlgebraicCurve_ComponentChart_exists_algEquiv_residue_eq_and_placeMap_eq_smul_of_integers_eq_of_dom_eq_of_hasDiscFibres
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_exists_algEquiv_residue_eq_and_placeMap_eq_smul_of_integers_eq_of_dom_eq_of_hasDiscFibres (solution)
