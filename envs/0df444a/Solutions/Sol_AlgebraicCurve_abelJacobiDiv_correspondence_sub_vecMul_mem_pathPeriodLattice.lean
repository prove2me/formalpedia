-- Prove2me | solution 1 for AlgebraicCurve.abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/37724d45-34c5-5f8a-958d-c5ba4cefdd3a

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice
import Theorems.Thm_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
import Theorems.Thm_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials
import Theorems.Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice.AlgebraicCurve"
open scoped Manifold Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along FiniteAlong Divisor.correspondence Place Place.FiniteResidue Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Differential.correspondence IsCurveOver IsCurveOver.instNontrivialKaehler IsCurveOver.forall_deg_eq_one_of_isAlgClosed Place.evalAt regularDifferentials mem_regularDifferentials_iff Place.chartRead_apply Place.readDifferential_apply IsPrimitiveAlong pathIntegral pathIntegral_def abelJacobiVec abelJacobiDiv abelJacobiDiv_single pathPeriodLattice exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice exists_isPrimitiveAlong_of_mem_regularDifferentials Differential.correspondence_mem_regularDifferentials isCurveOver_of_transcendental dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional"
namespace HurwitzGlobalProof
p2m_open "AlgebraicCurve"

theorem sub_mem_of_eventually_sub_mem {X M : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [AddCommGroup M] (L : AddSubgroup M) (φ : X → M)
    (h : ∀ x₀ : X, ∀ᶠ x in 𝓝 x₀, φ x - φ x₀ ∈ L) (x y : X) : φ x - φ y ∈ L := by
  let S : Set X := {x | φ x - φ y ∈ L}
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [h x] with x' hx'
    have : φ x' - φ y = (φ x' - φ x) + (φ x - φ y) := by abel
    show φ x' - φ y ∈ L
    rw [this]
    exact L.add_mem hx' hx
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [h x] with x' hx' hxS
    apply hx
    have : φ x - φ y = (φ x' - φ y) - (φ x' - φ x) := by abel
    show φ x - φ y ∈ L
    rw [this]
    exact L.sub_mem hxS hx'
  have hy : y ∈ S := by
    show φ y - φ y ∈ L
    rw [sub_self]
    exact L.zero_mem
  have hS : S = Set.univ := by
    rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with h0 | h1
    · exact absurd (h0 ▸ hy : y ∈ (∅ : Set X)) (Set.notMem_empty y)
    · exact h1
  have hx : x ∈ S := by rw [hS]; exact Set.mem_univ x
  exact hx

theorem sub_eq_sub_of_hasDerivAt_eq {f g : ℂ → ℂ} {f' : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : ∀ z ∈ Metric.ball c r, HasDerivAt f (f' z) z)
    (hg : ∀ z ∈ Metric.ball c r, HasDerivAt g (f' z) z)
    {z w : ℂ} (hz : z ∈ Metric.ball c r) (hw : w ∈ Metric.ball c r) :
    f z - g z = f w - g w := by
  have hdiff : DifferentiableOn ℂ (fun x => f x - g x) (Metric.ball c r) := fun x hx =>
    ((hf x hx).sub (hg x hx)).differentiableAt.differentiableWithinAt
  have hder : Set.EqOn (deriv fun x => f x - g x) 0 (Metric.ball c r) := fun x hx => by
    have := ((hf x hx).sub (hg x hx)).deriv
    simp at this
    exact this
  exact IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball c r).isPreconnected
    hdiff hder hz hw

section Algebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_not_isUnit (v : Place K F) {a : v.toValuationSubring} (ha : a ≠ 0)
    (hu : ¬IsUnit a) : 0 < v.ord (a : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu (by rw [pow_zero, mul_one]; exact u.isUnit)
  have hcoe : (((u : v.toValuationSubring) * π ^ n : v.toValuationSubring) : F) =
      ((u : v.toValuationSubring) : F) * (π : F) ^ (n : ℤ) := by
    rw [zpow_natCast, Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [hcoe, v.ord_unit_smul_zpow u hπ]
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
      have := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_mul
      simpa [hu] using this
    have h2 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← h2]
    exact SetLike.coe_mem _
  have ha : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    exact inv_ne_zero hf0 (by simpa using congrArg Subtype.val h)
  have := ord_pos_of_not_isUnit v ha hu
  rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl, v.ord_inv] at this
  omega

theorem finite_setOf_not_mem [HasPrincipalDivisors K F] (f : F) :
    {w : Place K F | f ∉ w.toValuationSubring}.Finite := by
  by_cases hf0 : f = 0
  · subst hf0
    convert Set.finite_empty
    ext w
    simp
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h := ord_neg_of_not_mem w hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h.ne

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem residue_algebraMap (w : Place K F) (a : K) :
    IsLocalRing.residue w.toValuationSubring
        (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.ResidueField a := by
  have h : (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.toValuationSubring a := Subtype.ext (w.coe_algebraMap a).symm
  rw [h]
  exact (IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField a).symm

theorem evalAt_algebraMap (w : Place K F) (a : K) : w.evalAt (algebraMap K F a) = a := by
  rw [w.evalAt_of_mem (w.algebraMap_mem' a), residue_algebraMap, w.residueInv_algebraMap]

theorem evalAt_add (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f + g) = w.evalAt f + w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (add_mem hf hg), map_add, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_add]
  rfl

theorem evalAt_mul (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f * g) = w.evalAt f * w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (mul_mem hf hg), map_mul, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_mul]
  rfl

theorem evalAt_sum_algebraMap_mul (w : Place K F) (hw : w.IsRational) {ι : Type*}
    (s : Finset ι) (c : ι → K) (h : ι → F) (hh : ∀ i ∈ s, h i ∈ w.toValuationSubring) :
    w.evalAt (∑ i ∈ s, algebraMap K F (c i) * h i) = ∑ i ∈ s, c i * w.evalAt (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalAt_algebraMap w (0 : K) |> fun h0 => by simpa using h0]
  | insert a s ha ih =>
      have hs : ∀ i ∈ s, h i ∈ w.toValuationSubring := fun i hi => hh i (Finset.mem_insert_of_mem hi)
      have hsum : (∑ i ∈ s, algebraMap K F (c i) * h i) ∈ w.toValuationSubring :=
        Subring.sum_mem _ fun i hi => mul_mem (w.algebraMap_mem' _) (hs i hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        evalAt_add w hw (mul_mem (w.algebraMap_mem' _) (hh a (Finset.mem_insert_self a s))) hsum,
        evalAt_mul w hw (w.algebraMap_mem' _) (hh a (Finset.mem_insert_self a s)),
        evalAt_algebraMap, ih hs]

theorem differentialCoeff_mem (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {η : Ω[F⁄K]} (hη : η ∈ regularDifferentials K F) :
    v.differentialCoeff η ∈ v.toValuationSubring := by
  obtain ⟨f, hf, hfe⟩ := (mem_regularDifferentials_iff (K := K) (F := F)).1 hη v
  rwa [v.differentialCoeff_unique hfe]

theorem differentialCoeff_sum_smul (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ι : Type*} (s : Finset ι) (c : ι → K) (η : ι → Ω[F⁄K]) :
    v.differentialCoeff (∑ i ∈ s, c i • η i) =
      ∑ i ∈ s, algebraMap K F (c i) * v.differentialCoeff (η i) := by
  apply v.differentialCoeff_unique
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul, v.differentialCoeff_smul_dCoord, algebraMap_smul]

end Algebra

section Charts

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]

omit [ChartedSpace ℂ (Place ℂ F)] in

theorem isOpen_setOf_mem (f : F) : IsOpen {w : Place ℂ F | f ∈ w.toValuationSubring} := by
  have h : {w : Place ℂ F | f ∈ w.toValuationSubring} =
      {w : Place ℂ F | f ∉ w.toValuationSubring}ᶜ := by
    ext w; simp
  rw [h]
  exact (finite_setOf_not_mem (K := ℂ) f).isClosed.isOpen_compl

theorem eventually_forall_mem {ι : Type*} [Finite ι] (P : Place ℂ F) (h : ι → F)
    (hh : ∀ i, h i ∈ P.toValuationSubring) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) P P),
      ∀ i, h i ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring := by
  have hc : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P) :=
    continuousAt_extChartAt_symm P
  have hopen : IsOpen (⋂ i, {w : Place ℂ F | h i ∈ w.toValuationSubring}) :=
    isOpen_iInter_of_finite fun i => isOpen_setOf_mem (h i)
  have hmem : (⋂ i, {w : Place ℂ F | h i ∈ w.toValuationSubring}) ∈
      𝓝 ((extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P)) := by
    rw [extChartAt_to_inv]
    exact hopen.mem_nhds (Set.mem_iInter.2 hh)
  filter_upwards [hc.preimage_mem_nhds hmem] with z hz
  exact fun i => Set.mem_iInter.1 hz i

omit [T2Space (Place ℂ F)] in

theorem readDifferential_sum_smul (P : Place ℂ F) [P.DCoordGenerates] {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (η : ι → Ω[F⁄ℂ]) {z : ℂ}
    (hz : ∀ i ∈ s, P.differentialCoeff (η i) ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring) :
    P.readDifferential (∑ i ∈ s, c i • η i) z = ∑ i ∈ s, c i * P.readDifferential (η i) z := by
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F)
  set Q : Place ℂ F := (extChartAt 𝓘(ℂ, ℂ) P).symm z with hQ
  have hQrat : Q.IsRational := isRational_of_isAlgClosed Q
  simp only [Place.readDifferential_apply, Place.chartRead_apply]
  rw [differentialCoeff_sum_smul, ← hQ, evalAt_sum_algebraMap_mul Q hQrat s c _ hz,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Charts

section Primitives

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]

def PrimOK (η : Ω[F⁄ℂ]) : Prop :=
  ∀ {P Q : Place ℂ F} (γ : Path P Q),
    (∃ g : unitInterval → ℂ, IsPrimitiveAlong η γ g) ∧
      ∀ g g' : unitInterval → ℂ, IsPrimitiveAlong η γ g → IsPrimitiveAlong η γ g' →
        ∀ t, g t - g' t = g 0 - g' 0

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] in
theorem pathIntegral_eq {η : Ω[F⁄ℂ]} (hη : PrimOK η) {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong η γ g) : pathIntegral η γ = g 1 - g 0 := by
  have h : ∃ g : unitInterval → ℂ, IsPrimitiveAlong η γ g := ⟨g, hg⟩
  rw [pathIntegral_def, dif_pos h]
  have := (hη γ).2 _ _ h.choose_spec hg 1
  linear_combination this

theorem isPrimitiveAlong_sum_smul (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (η : ι → Ω[F⁄ℂ])
    (hη : ∀ i, η i ∈ regularDifferentials ℂ F) {P Q : Place ℂ F} (γ : Path P Q)
    (g : ι → unitInterval → ℂ) (hg : ∀ i, IsPrimitiveAlong (η i) γ (g i)) :
    IsPrimitiveAlong (∑ i, c i • η i) γ (fun t => ∑ i, c i * g i t) := by
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F)
  intro t₀
  haveI := hgen (γ t₀)
  choose Φ hΦ hgΦ using fun i => hg i t₀
  refine ⟨fun z => ∑ i, c i * Φ i z, ?_, ?_⟩
  · have hgood := eventually_forall_mem (γ t₀) (fun i => (γ t₀).differentialCoeff (η i))
      (fun i => differentialCoeff_mem (γ t₀) (hη i))
    filter_upwards [Filter.eventually_all.2 hΦ, hgood] with z hz hz'
    rw [readDifferential_sum_smul (γ t₀) Finset.univ c η (fun i _ => hz' i)]
    exact HasDerivAt.fun_sum fun i _ => (hz i).const_mul (c i)
  · filter_upwards [Filter.eventually_all.2 hgΦ] with t ht
    simp only [ht]

end Primitives

section Main

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) (Place ℂ F)] [CompactSpace (Place ℂ F)]
variable [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]

def vecMulHom {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) : (Fin n → ℂ) →+ (Fin n → ℂ) :=
  AddMonoidHom.mk' (fun u => Matrix.vecMul u S) fun x y => Matrix.add_vecMul S x y

@[scoped simp] theorem vecMulHom_apply {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    vecMulHom S u = Matrix.vecMul u S := rfl

end Main

end AlgebraicCurve.HurwitzGlobalProof
p2m_reactivate "P2MW.S_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice.AlgebraicCurve P2MW.S_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice.AlgebraicCurve.HurwitzGlobalProof"
p2m_reactivate "P2MW.S_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice.AlgebraicCurve"

open AlgebraicCurve.HurwitzGlobalProof in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (F' : Type*) [Field F'] [Algebra ℂ F'] [HasPrincipalDivisors ℂ F']
    (φ ψ : F →ₐ[ℂ] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ ψ)
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ j : Fin n, Differential.correspondence φ ψ (b j : Ω[F⁄ℂ]) =
      ∑ k : Fin n, S k j • (b k : Ω[F⁄ℂ])) :
    (∀ u ∈ pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])),
        Matrix.vecMul u S ∈ pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ]))) ∧
    ∀ D : Divisor ℂ F, Divisor.degree D = 0 →
      abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ (Divisor.correspondence φ ψ hφ hψ D) -
          Matrix.vecMul (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D) S ∈
        pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) := by
  classical

  set bΩ : Fin n → Ω[F⁄ℂ] := fun i => (b i : Ω[F⁄ℂ]) with hbΩ
  have hb : ∀ i, bΩ i ∈ regularDifferentials ℂ F := fun i => (b i).2
  set T : Divisor ℂ F →+ Divisor ℂ F := Divisor.correspondence φ ψ hφ hψ with hT
  set TΩ : Ω[F⁄ℂ] →ₗ[ℂ] Ω[F⁄ℂ] := Differential.correspondence φ ψ with hTΩ
  set AJ : Divisor ℂ F →+ (Fin n → ℂ) := abelJacobiDiv bΩ P₀ with hAJ
  set Λ : Submodule ℤ (Fin n → ℂ) := pathPeriodLattice bΩ with hΛ
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F)
  have hgen : ∀ v : Place ℂ F, v.DCoordGenerates := by
    obtain ⟨x, hx, hfd⟩ := hfg
    haveI := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
    exact AlgebraicCurve.dCoordGenerates_of_isCurveOver

  haveI : IsCurveOver ℂ F' := by

    obtain ⟨x, hx, hxfin⟩ := hfg
    letI : Algebra F F' := algebraAlong ψ
    haveI := isScalarTower_along ψ
    haveI : Module.Finite F F' := hfin
    set Kx : IntermediateField ℂ F := IntermediateField.adjoin ℂ ({x} : Set F) with hKx
    set y : F' := ψ x with hy_def
    set Ky : IntermediateField ℂ F' := IntermediateField.adjoin ℂ ({y} : Set F') with hKy
    have hy : Transcendental ℂ y := fun h =>
      hx ((isAlgebraic_algHom_iff ψ ψ.toRingHom.injective).mp h)
    have hmap : ∀ z ∈ Kx, ψ z ∈ Ky := by
      intro z hz
      have hKxy : Kx.map ψ = Ky := by
        rw [hKx, IntermediateField.adjoin_map, Set.image_singleton]
      rw [← hKxy]
      exact ⟨z, hz, rfl⟩
    let f : Kx →+* Ky := ψ.toRingHom.restrict Kx Ky hmap
    letI algKxF' : Algebra Kx F' := ((algebraMap F F').comp (algebraMap Kx F)).toAlgebra
    haveI : IsScalarTower Kx F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite Kx F' := Module.Finite.trans F F'
    letI : Algebra Kx Ky := f.toAlgebra
    haveI : IsScalarTower Kx Ky F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hfd : FiniteDimensional Ky F' := Module.Finite.of_restrictScalars_finite Kx Ky F'
    have hsep : Algebra.IsSeparable Ky F' := by
      haveI : FiniteDimensional Ky F' := hfd
      infer_instance
    exact AlgebraicCurve.isCurveOver_of_transcendental hy hfd hsep
  have hTb : ∀ j, TΩ (bΩ j) ∈ regularDifferentials ℂ F := fun j =>
    AlgebraicCurve.Differential.correspondence_mem_regularDifferentials ℂ F F' hfg φ ψ hφ hψ hfin
      (hb j)

  have hprim : ∀ i, PrimOK (bΩ i) := fun i {P Q} γ =>
    AlgebraicCurve.exists_isPrimitiveAlong_of_mem_regularDifferentials F hfg hF (bΩ i) (hb i) γ
  have hprimT : ∀ j, PrimOK (TΩ (bΩ j)) := fun j {P Q} γ =>
    AlgebraicCurve.exists_isPrimitiveAlong_of_mem_regularDifferentials F hfg hF _ (hTb j) γ

  have hS' : ∀ j, TΩ (bΩ j) = ∑ k, S k j • bΩ k := hS

  have hlocal : ∀ P : Place ℂ F, ∃ r : ℝ, 0 < r ∧
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target ∧
      ∃ (G Φ : Fin n → ℂ → ℂ),
        (∀ j, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          HasDerivAt (G j) (P.readDifferential (TΩ (bΩ j)) z) z) ∧
        (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          AJ (T (Finsupp.single ((extChartAt 𝓘(ℂ, ℂ) P).symm z) 1)) - AJ (T (Finsupp.single P 1)) -
            (fun j => G j z - G j (extChartAt 𝓘(ℂ, ℂ) P P)) ∈ Λ) ∧
        (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          abelJacobiVec bΩ P₀ ((extChartAt 𝓘(ℂ, ℂ) P).symm z) - abelJacobiVec bΩ P₀ P -
            (fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) P P)) ∈ Λ) ∧
        (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r, ∀ j,
          G j z - ∑ i, S i j * Φ i z =
            G j (extChartAt 𝓘(ℂ, ℂ) P P) - ∑ i, S i j * Φ i (extChartAt 𝓘(ℂ, ℂ) P P)) := by
    intro P
    haveI := hgen P
    obtain ⟨r₁, hr₁, htar₁, G, hG, hGAJ⟩ :=
      AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice F hfg
        hF F' φ ψ hφ hψ hfin bΩ hb P₀ P
    obtain ⟨r₂, hr₂, -, Φ, hΦ, hΦAJ⟩ :=
      AlgebraicCurve.exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice F hfg hF bΩ hb P₀ P

    obtain ⟨r₃, hr₃, hgood⟩ : ∃ r₃ : ℝ, 0 < r₃ ∧ ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r₃,
        ∀ i, P.differentialCoeff (bΩ i) ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring :=
      Metric.eventually_nhds_iff_ball.1 (eventually_forall_mem P (fun i => P.differentialCoeff (bΩ i))
        (fun i => differentialCoeff_mem P (hb i)))
    set r := min r₁ (min r₂ r₃) with hr
    have hrpos : 0 < r := lt_min hr₁ (lt_min hr₂ hr₃)
    have hb₁ : Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r₁ :=
      Metric.ball_subset_ball (min_le_left _ _)
    have hb₂ : Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r₂ :=
      Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
    have hb₃ : Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r₃ :=
      Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨r, hrpos, hb₁.trans htar₁, G, Φ, fun j z hz => hG j z (hb₁ hz),
      fun z hz => hGAJ z (hb₁ hz), fun z hz => hΦAJ z (hb₂ hz), fun z hz j => ?_⟩

    have hc : extChartAt 𝓘(ℂ, ℂ) P P ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r :=
      Metric.mem_ball_self hrpos
    refine sub_eq_sub_of_hasDerivAt_eq (f' := fun w => P.readDifferential (TΩ (bΩ j)) w)
      (g := fun w => ∑ i, S i j * Φ i w) (fun w hw => hG j w (hb₁ hw)) (fun w hw => ?_) hz hc
    have hread : P.readDifferential (TΩ (bΩ j)) w = ∑ i, S i j * P.readDifferential (bΩ i) w := by
      rw [hS', readDifferential_sum_smul P Finset.univ (fun k => S k j) bΩ
        (fun i _ => hgood w (hb₃ hw) i)]
    show HasDerivAt (fun w => ∑ i, S i j * Φ i w) (P.readDifferential (TΩ (bΩ j)) w) w
    rw [hread]
    exact HasDerivAt.fun_sum fun i _ => (hΦ i w (hb₂ hw)).const_mul (S i j)

  have hpart1 : ∀ u ∈ Λ, Matrix.vecMul u S ∈ Λ := by
    intro u hu

    induction hu using Submodule.span_induction with
    | zero => rw [Matrix.zero_vecMul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.add_vecMul]; exact Submodule.add_mem _ hx hy
    | smul m x _ hx => rw [Matrix.smul_vecMul]; exact Submodule.smul_mem _ m hx
    | mem x hx =>
    obtain ⟨P, γ, rfl⟩ := hx

    choose g hg using fun i => (hprim i γ).1
    choose k hk using fun j => (hprimT j γ).1

    have hk' : ∀ j, IsPrimitiveAlong (TΩ (bΩ j)) γ (fun t => ∑ i, S i j * g i t) := fun j => by
      rw [hS']
      exact isPrimitiveAlong_sum_smul hgen (fun i => S i j) bΩ hb γ g hg
    have hkS : (fun j => k j 1 - k j 0) = Matrix.vecMul (fun i => pathIntegral (bΩ i) γ) S := by
      funext j
      have h := (hprimT j γ).2 _ _ (hk j) (hk' j) 1
      simp only [Matrix.vecMul, dotProduct, pathIntegral_eq (hprim _) (hg _)]
      have : k j 1 - k j 0 = ∑ i, S i j * g i 1 - ∑ i, S i j * g i 0 := by linear_combination h
      rw [this, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring

    have hkΛ : (fun j => k j 1 - k j 0) ∈ Λ := by
      set E : unitInterval → (Fin n → ℂ) := fun t => AJ (T (Finsupp.single (γ t) 1)) - fun j => k j t
        with hE
      have hchain : ∀ t₀ : unitInterval, ∀ᶠ t in 𝓝 t₀, E t - E t₀ ∈ Λ.toAddSubgroup := by
        intro t₀
        set Q : Place ℂ F := γ t₀ with hQ
        obtain ⟨r, hr, htar, G, Φ, hG, hGAJ, -, -⟩ := hlocal Q

        choose Ψ hΨ hkΨ using fun j => hk j t₀
        simp only [← hQ] at hΨ hkΨ

        obtain ⟨ρ, hρ, hρr, hΨ'⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ j, ∀ w ∈ Metric.ball
            (extChartAt 𝓘(ℂ, ℂ) Q Q) ρ, HasDerivAt (Ψ j) (Q.readDifferential (TΩ (bΩ j)) w) w := by
          have hall := Filter.eventually_all.2 hΨ
          obtain ⟨ρ₀, hρ₀, hρ₀'⟩ := Metric.eventually_nhds_iff_ball.1 hall
          exact ⟨min ρ₀ r, lt_min hρ₀ hr, min_le_right _ _, fun j w hw =>
            hρ₀' w (Metric.ball_subset_ball (min_le_left _ _) hw) j⟩
        have hcst : ∀ j, ∀ w ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) Q Q) ρ,
            G j w - Ψ j w = G j (extChartAt 𝓘(ℂ, ℂ) Q Q) - Ψ j (extChartAt 𝓘(ℂ, ℂ) Q Q) :=
          fun j w hw => sub_eq_sub_of_hasDerivAt_eq
            (fun w' hw' => hG j w' (Metric.ball_subset_ball hρr hw')) (hΨ' j) hw
            (Metric.mem_ball_self hρ)

        have hsrc : ∀ᶠ t in 𝓝 t₀, γ t ∈ (extChartAt 𝓘(ℂ, ℂ) Q).source := by
          apply γ.continuous.continuousAt.preimage_mem_nhds
          rw [← hQ]
          exact (isOpen_extChartAt_source Q).mem_nhds (mem_extChartAt_source Q)
        have hball : ∀ᶠ t in 𝓝 t₀, extChartAt 𝓘(ℂ, ℂ) Q (γ t) ∈
            Metric.ball (extChartAt 𝓘(ℂ, ℂ) Q Q) ρ := by
          have hc : ContinuousAt (fun t => extChartAt 𝓘(ℂ, ℂ) Q (γ t)) t₀ := by
            refine (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) Q).comp_of_eq γ.continuous.continuousAt ?_
            rw [hQ]
          apply hc.preimage_mem_nhds
          rw [← hQ]
          exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
        have hkt₀ : ∀ j, k j t₀ = Ψ j (extChartAt 𝓘(ℂ, ℂ) Q Q) := fun j => by
          have h := ((Filter.eventually_all.2 hkΨ).self_of_nhds : _) j
          rw [h, ← hQ]
        filter_upwards [hsrc, hball, Filter.eventually_all.2 hkΨ] with t ht hbt hkt
        set z : ℂ := extChartAt 𝓘(ℂ, ℂ) Q (γ t) with hz
        have hγt : (extChartAt 𝓘(ℂ, ℂ) Q).symm z = γ t := (extChartAt 𝓘(ℂ, ℂ) Q).left_inv ht
        have h1 := hGAJ z (Metric.ball_subset_ball hρr hbt)
        rw [hγt] at h1
        have hk_eq : ((fun j => k j t) - fun j => k j t₀) =
            fun j => G j z - G j (extChartAt 𝓘(ℂ, ℂ) Q Q) := by
          funext j
          simp only [Pi.sub_apply, hkt j, hkt₀ j]
          have := hcst j z hbt
          linear_combination -this
        have hEt : E t - E t₀ = AJ (T (Finsupp.single (γ t) 1)) - AJ (T (Finsupp.single Q 1)) -
            ((fun j => k j t) - fun j => k j t₀) := by
          simp only [hE]
          rw [← hQ]
          abel
        show E t - E t₀ ∈ Λ
        rw [hEt, hk_eq]
        exact h1
      have h := sub_mem_of_eventually_sub_mem Λ.toAddSubgroup E hchain 1 0
      have hE10 : E 1 - E 0 = -(fun j => k j 1 - k j 0) := by
        simp only [E, γ.source, γ.target]
        funext j
        simp only [Pi.sub_apply, Pi.neg_apply]
        ring
      rw [hE10] at h
      simpa using Λ.toAddSubgroup.neg_mem h
    rw [hkS] at hkΛ
    exact hkΛ
  refine ⟨hpart1, ?_⟩

  set δ : Divisor ℂ F →+ (Fin n → ℂ) := AJ.comp T - (vecMulHom S).comp AJ with hδ
  have hδapply : ∀ D, δ D = AJ (T D) - Matrix.vecMul (AJ D) S := fun D => rfl

  set f : Place ℂ F → (Fin n → ℂ) := fun Q => δ (Finsupp.single Q 1) with hf
  have hAJsingle : ∀ Q, AJ (Finsupp.single Q 1) = abelJacobiVec bΩ P₀ Q := fun Q => by
    simp only [hAJ, abelJacobiDiv_single, one_smul]
  have hfloc : ∀ P : Place ℂ F, ∀ᶠ Q in 𝓝 P, f Q - f P ∈ Λ.toAddSubgroup := by
    intro P
    obtain ⟨r, hr, htar, G, Φ, -, hGAJ, hΦAJ, hcst⟩ := hlocal P

    have hsrc : ∀ᶠ Q in 𝓝 P, Q ∈ (extChartAt 𝓘(ℂ, ℂ) P).source :=
      (isOpen_extChartAt_source P).mem_nhds (mem_extChartAt_source P)
    have hball : ∀ᶠ Q in 𝓝 P, extChartAt 𝓘(ℂ, ℂ) P Q ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r :=
      (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) P).preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    filter_upwards [hsrc, hball] with Q hQ hzQ
    set z : ℂ := extChartAt 𝓘(ℂ, ℂ) P Q with hz
    have hQz : (extChartAt 𝓘(ℂ, ℂ) P).symm z = Q := (extChartAt 𝓘(ℂ, ℂ) P).left_inv hQ
    have h1 := hGAJ z hzQ
    have h2 := hΦAJ z hzQ
    have h3 := hpart1 _ h2
    rw [hQz] at h1 h2 h3

    have hlast : (fun j => G j z - G j (extChartAt 𝓘(ℂ, ℂ) P P)) -
        Matrix.vecMul (fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) P P)) S = 0 := by
      funext j
      simp only [Pi.sub_apply, Pi.zero_apply, Matrix.vecMul, dotProduct]
      have := hcst z hzQ j
      have e : ∑ x, (Φ x z - Φ x (extChartAt 𝓘(ℂ, ℂ) P P)) * S x j =
          ∑ i, S i j * Φ i z - ∑ i, S i j * Φ i (extChartAt 𝓘(ℂ, ℂ) P P) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      linear_combination this
    show f Q - f P ∈ Λ
    have key : f Q - f P =
        (AJ (T (Finsupp.single Q 1)) - AJ (T (Finsupp.single P 1)) -
            fun j => G j z - G j (extChartAt 𝓘(ℂ, ℂ) P P)) -
          Matrix.vecMul (abelJacobiVec bΩ P₀ Q - abelJacobiVec bΩ P₀ P -
            fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) P P)) S +
          ((fun j => G j z - G j (extChartAt 𝓘(ℂ, ℂ) P P)) -
            Matrix.vecMul (fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) P P)) S) := by
      simp only [hf, hδapply, hAJsingle, Matrix.sub_vecMul]
      abel
    rw [key, hlast, add_zero]
    exact Λ.sub_mem h1 h3

  haveI : PreconnectedSpace (Place ℂ F) := inferInstance
  have hfglob : ∀ Q, f Q - f P₀ ∈ Λ := fun Q =>
    sub_mem_of_eventually_sub_mem Λ.toAddSubgroup f hfloc Q P₀

  have hδdiff : ∀ Q, δ (Finsupp.single Q 1 - Finsupp.single P₀ 1) ∈ Λ := fun Q => by
    rw [map_sub]; exact hfglob Q

  have hdeg : ∀ D : Divisor ℂ F, D.degree = D.sum fun _ m => m := by

    intro D
    induction D using Finsupp.induction with
    | zero => simp
    | single_add v m D' hv hm ih =>
        rw [map_add, Divisor.degree_single, IsCurveOver.forall_deg_eq_one_of_isAlgClosed (K := ℂ) v,
          Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
          ih]
        simp
  intro D hD
  have hDsum : D = D.sum fun v m => m • (Finsupp.single v 1 - Finsupp.single P₀ 1) := by
    have h1 : (D.sum fun v m => m • (Finsupp.single v 1 - Finsupp.single P₀ 1)) =
        (D.sum fun v m => Finsupp.single v m) - (D.sum fun _ m => m) • Finsupp.single P₀ 1 := by
      simp only [Finsupp.sum, smul_sub, Finsupp.smul_single_one, Finset.sum_sub_distrib,
        Finset.sum_smul]
    rw [h1, Finsupp.sum_single, ← hdeg D, hD, zero_smul, sub_zero]
  show δ D ∈ Λ
  rw [hDsum, map_finsuppSum]
  apply Submodule.finsuppSum_mem
  intro v _
  rw [map_zsmul]
  exact Λ.smul_mem _ (hδdiff v)

end
end S_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice
end P2MW
export P2MW.S_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice (solution)
