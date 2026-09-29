-- Prove2me | solution 1 for AlgebraicCurve.exists_eventuallyEq_evalAt_of_meromorphicAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/18531d46-e493-5373-925c-6335ea7dd9a3

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card
import Theorems.Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_ell_sub_ell_le_degree_sub_degree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt.AlgebraicCurve Filter Topology Set"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.FiniteResidue Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed Place.evalAt Place.evalAt_one mem_riemannRochSpace_iff genusFF LSpace ell exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental ell_sub_ell_le_degree_sub_degree"
namespace GAGAProof
p2m_open "AlgebraicCurve"

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
  have hinv : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
        have := congrArg (fun a : v.toValuationSubring => (a : F)) (u.inv_mul)
        simpa [hu] using this
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← this]
    exact SetLike.coe_mem _
  have ha : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    exact inv_ne_zero hf0 (by simpa using congrArg Subtype.val h)
  have := ord_pos_of_not_isUnit v ha hu
  rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl, v.ord_inv] at this
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  exact absurd (ord_neg_of_not_mem v hf) (not_lt.2 h)

theorem finite_setOf_not_mem [HasPrincipalDivisors K F] {f : F} (hf0 : f ≠ 0) :
    {w : Place K F | f ∉ w.toValuationSubring}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h := ord_neg_of_not_mem w hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h.ne

theorem finite_setOf_ord_ne_zero [HasPrincipalDivisors K F] {f : F} (hf0 : f ≠ 0) :
    {w : Place K F | w.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h : w.ord f ≠ 0 := hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h

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

theorem evalAt_algebraMap' (w : Place K F) (a : K) : w.evalAt (algebraMap K F a) = a := by
  rw [w.evalAt_of_mem (w.algebraMap_mem' a), residue_algebraMap, w.residueInv_algebraMap]

theorem evalAt_zero' (w : Place K F) : w.evalAt (0 : F) = 0 := by
  simpa using evalAt_algebraMap' w (0 : K)

theorem evalAt_mul (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f * g) = w.evalAt f * w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (mul_mem hf hg), map_mul, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_mul]
  rfl

theorem evalAt_add (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f + g) = w.evalAt f + w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (add_mem hf hg), map_add, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_add]
  rfl

theorem evalAt_ne_zero_of_ord_eq_zero (w : Place K F) (hw : w.IsRational) {f : F} (hf0 : f ≠ 0)
    (h : w.ord f = 0) : w.evalAt f ≠ 0 := by
  intro h0
  have hf : f ∈ w.toValuationSubring := mem_of_ord_nonneg w h.ge
  have hres : IsLocalRing.residue w.toValuationSubring ⟨f, hf⟩ = 0 := by
    have h := w.algebraMap_evalAt hw hf
    rw [h0, map_zero] at h
    exact h.symm
  have ha : (⟨f, hf⟩ : w.toValuationSubring) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hu : ¬IsUnit (⟨f, hf⟩ : w.toValuationSubring) := by
    rw [IsLocalRing.residue_eq_zero_iff] at hres
    exact (IsLocalRing.mem_maximalIdeal _).1 hres
  have key := ord_pos_of_not_isUnit w ha hu
  have key' : 0 < w.ord f := key
  omega

end Algebra

section Surface

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

abbrev φ (v : Place ℂ F) : PartialEquiv (Place ℂ F) ℂ := extChartAt 𝓘(ℂ, ℂ) v

abbrev ctr (v : Place ℂ F) : ℂ := extChartAt 𝓘(ℂ, ℂ) v v

abbrev pf (w : Place ℂ F) : Filter ℂ := 𝓝[≠] (ctr w)

abbrev read (v : Place ℂ F) (f : F) : ℂ → ℂ := fun z => Place.evalAt ((φ v).symm z) f

abbrev rd (ψ : Place ℂ F → ℂ) (v : Place ℂ F) : ℂ → ℂ := fun z => ψ ((φ v).symm z)

def ChartCompatible (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

theorem read_zero (w : Place ℂ F) : read w (0 : F) = 0 :=
  funext fun _ => evalAt_zero' _

theorem meromorphicAt_read (hF : ChartCompatible F) (w : Place ℂ F) (f : F) :
    MeromorphicAt (read w f) (ctr w) := by
  by_cases hf : f = 0
  · rw [hf, read_zero]; exact MeromorphicAt.const 0 _
  · exact (hF f hf w).1

theorem meromorphicOrderAt_read (hF : ChartCompatible F) (w : Place ℂ F) {f : F} (hf : f ≠ 0) :
    meromorphicOrderAt (read w f) (ctr w) = (w.ord f : ℤ) :=
  (hF f hf w).2

theorem eq_zero_of_read_eventuallyEq_zero (hF : ChartCompatible F) (w : Place ℂ F) {f : F}
    (h : read w f =ᶠ[pf w] 0) : f = 0 := by
  by_contra hf
  have h1 := meromorphicOrderAt_read hF w hf
  rw [meromorphicOrderAt_eq_top_iff.2 h] at h1
  exact WithTop.top_ne_coe h1

variable [IsCurveOver ℂ F]

omit [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] in
theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isAlgClosed w

variable [T2Space (Place ℂ F)]

omit [ChartedSpace ℂ (Place ℂ F)] [IsCurveOver ℂ F] in

theorem eventually_nhdsWithin_compl_not_mem {S : Set (Place ℂ F)} (hS : S.Finite)
    (w : Place ℂ F) : ∀ᶠ u in 𝓝[≠] w, u ∉ S := by
  have hfin : (S \ {w}).Finite := hS.subset diff_subset
  have hopen : IsOpen (S \ {w})ᶜ := hfin.isClosed.isOpen_compl
  have hmem : w ∈ (S \ {w})ᶜ := fun h => h.2 rfl
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hopen.mem_nhds hmem] with u hu hne
  intro huS
  exact hu ⟨huS, hne⟩

omit [IsCurveOver ℂ F] [T2Space (Place ℂ F)] in

theorem eventually_pf_of_eventually_nhdsWithin {P : Place ℂ F → Prop} (w : Place ℂ F)
    (h : ∀ᶠ u in 𝓝[≠] w, P u) : ∀ᶠ z in pf w, P ((φ w).symm z) := by
  rw [eventually_nhdsWithin_iff] at h
  have h1 : ∀ᶠ z in 𝓝 (ctr w), (φ w).symm z ≠ w → P ((φ w).symm z) := by
    have hc : ContinuousAt (φ w).symm (ctr w) := continuousAt_extChartAt_symm w
    have h' : ∀ᶠ u in 𝓝 ((φ w).symm (ctr w)), u ≠ w → P u := by
      rw [extChartAt_to_inv]; exact h
    exact hc.eventually h'
  have h2 : ∀ᶠ z in 𝓝 (ctr w), z ∈ (φ w).target := extChartAt_target_mem_nhds w
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h1, h2] with z hz hzt hne
  refine hz fun heq => hne ?_
  have : φ w ((φ w).symm z) = z := (φ w).right_inv hzt
  rw [mem_singleton_iff, ← this, heq]

theorem eventually_mem_punctured (f : F) (w : Place ℂ F) :
    ∀ᶠ z in pf w, f ∈ ((φ w).symm z).toValuationSubring := by
  by_cases hf0 : f = 0
  · exact Eventually.of_forall fun z => by rw [hf0]; exact zero_mem _
  refine eventually_pf_of_eventually_nhdsWithin (P := fun u => f ∈ u.toValuationSubring) w ?_
  filter_upwards [eventually_nhdsWithin_compl_not_mem (finite_setOf_not_mem (K := ℂ) hf0) w]
    with u hu
  simpa using hu

theorem eventually_ord_eq_zero_punctured {f : F} (hf : f ≠ 0) (w : Place ℂ F) :
    ∀ᶠ z in pf w, ((φ w).symm z).ord f = 0 := by
  refine eventually_pf_of_eventually_nhdsWithin (P := fun u => u.ord f = 0) w ?_
  filter_upwards [eventually_nhdsWithin_compl_not_mem (finite_setOf_ord_ne_zero (K := ℂ) hf) w]
    with u hu
  simpa using hu

theorem read_mul (w : Place ℂ F) (f g : F) : read w (f * g) =ᶠ[pf w] read w f * read w g := by
  filter_upwards [eventually_mem_punctured f w, eventually_mem_punctured g w] with z hf hg
  exact evalAt_mul _ (isRational _) hf hg

theorem read_add (w : Place ℂ F) (f g : F) : read w (f + g) =ᶠ[pf w] read w f + read w g := by
  filter_upwards [eventually_mem_punctured f w, eventually_mem_punctured g w] with z hf hg
  exact evalAt_add _ (isRational _) hf hg

theorem read_smul (w : Place ℂ F) (a : ℂ) (f : F) : read w (a • f) =ᶠ[pf w] a • read w f := by
  rw [Algebra.smul_def]
  filter_upwards [read_mul w (algebraMap ℂ F a) f] with z hz
  rw [hz, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  simp only [read, evalAt_algebraMap']

theorem read_inv (w : Place ℂ F) {f : F} (hf : f ≠ 0) : read w f⁻¹ =ᶠ[pf w] (read w f)⁻¹ := by
  have h := read_mul w f⁻¹ f
  rw [inv_mul_cancel₀ hf] at h
  filter_upwards [h] with z hz
  simp only [read, Place.evalAt_one, Pi.mul_apply] at hz
  rw [Pi.inv_apply]
  exact eq_inv_of_mul_eq_one_left hz.symm

theorem read_neg (w : Place ℂ F) (f : F) : read w (-f) =ᶠ[pf w] -read w f := by
  have h := read_smul w (-1) f
  rw [neg_one_smul] at h
  filter_upwards [h] with z hz
  rw [hz, Pi.smul_apply, smul_eq_mul, neg_one_mul, Pi.neg_apply]

theorem read_ne_zero (w : Place ℂ F) {f : F} (hf : f ≠ 0) : ∀ᶠ z in pf w, read w f z ≠ 0 := by
  filter_upwards [eventually_ord_eq_zero_punctured hf w] with z hz
  exact evalAt_ne_zero_of_ord_eq_zero _ (isRational _) hf hz

theorem read_sum {ι : Type*} (s : Finset ι) (w : Place ℂ F) (c : ι → ℂ) (f : ι → F) :
    read w (∑ i ∈ s, c i • f i) =ᶠ[pf w] fun z => ∑ i ∈ s, c i * read w (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, read_zero]
    exact Eventually.of_forall fun _ => rfl
  | insert i s hi ih =>
    filter_upwards [ih, read_add w (c i • f i) (∑ j ∈ s, c j • f j), read_smul w (c i) (f i)]
      with z hz hadd hsmul
    rw [Finset.sum_insert hi, hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hz,
      Finset.sum_insert hi]

end Surface

section Global

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem exists_ball_of_eventually_pf (v : Place ℂ F) {P : ℂ → Prop} (h : ∀ᶠ z in pf v, P z) :
    ∃ r > 0, Metric.ball (ctr v) r ⊆ (φ v).target ∧
      ∀ z ∈ Metric.ball (ctr v) r, z ≠ ctr v → P z := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h.and (extChartAt_target_mem_nhds v))
  exact ⟨r, hr, fun z hz => (hball z hz).2, fun z hz hne => (hball z hz).1 hne⟩

theorem eventually_mem_source_and_ball (v : Place ℂ F) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ w in 𝓝 v, w ∈ (φ v).source ∧ φ v w ∈ Metric.ball (ctr v) r ∧ (w ≠ v → φ v w ≠ ctr v) := by
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) v,
    (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) v).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)]
    with w hw hb
  exact ⟨hw, hb, fun hne heq => hne ((φ v).injOn hw (mem_extChartAt_source v) heq)⟩

theorem rd_eq_comp (ψ : Place ℂ F → ℂ) {v w : Place ℂ F} {z : ℂ} (hz : (φ w).symm z ∈ (φ v).source) :
    rd ψ w z = rd ψ v (φ v ((φ w).symm z)) := by
  simp only [rd]
  rw [(φ v).left_inv hz]

theorem eventually_symm_mem_source {v w : Place ℂ F} {y : ℂ} (hy : y ∈ (φ w).target)
    (hv : (φ w).symm y ∈ (φ v).source) : ∀ᶠ z in 𝓝 y, (φ w).symm z ∈ (φ v).source :=
  (continuousAt_extChartAt_symm'' hy).preimage_mem_nhds (extChartAt_source_mem_nhds' hv)

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem analyticAt_transition (u v : Place ℂ F) {y : ℂ} (hy : y ∈ (φ v).target)
    (hu : (φ v).symm y ∈ (φ u).source) : AnalyticAt ℂ (φ u ∘ (φ v).symm) y := by
  have hcd := contDiffOn_ext_coord_change (I := 𝓘(ℂ, ℂ)) (n := ω) u v
  have hsrc : ((φ v).symm ≫ φ u).source ∈ 𝓝 y := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    refine Filter.inter_mem (extChartAt_target_mem_nhds' hy) ?_
    exact (continuousAt_extChartAt_symm'' hy).preimage_mem_nhds (extChartAt_source_mem_nhds' hu)
  exact (hcd.contDiffAt hsrc).analyticAt

omit [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem rd_change (ψ : Place ℂ F → ℂ) {v w : Place ℂ F} (hw : w ∈ (φ v).source) :
    rd ψ w =ᶠ[𝓝 (ctr w)] (rd ψ v ∘ (φ v ∘ (φ w).symm)) := by
  have hs : ∀ᶠ z in 𝓝 (ctr w), (φ w).symm z ∈ (φ v).source :=
    eventually_symm_mem_source (mem_extChartAt_target w) (by rw [extChartAt_to_inv]; exact hw)
  filter_upwards [hs] with z hz
  exact rd_eq_comp ψ hz

theorem eventually_order_eq_top (ψ : Place ℂ F → ℂ) {v : Place ℂ F} (hv : rd ψ v =ᶠ[pf v] 0) :
    ∀ᶠ w in 𝓝 v, meromorphicOrderAt (rd ψ w) (ctr w) = ⊤ := by

  have h1 : ∀ᶠ z in pf v, ∀ᶠ z' in 𝓝 z, rd ψ v z' = 0 := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at hv
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hv.eventually_nhds] with z hz hne
    have hne' : ∀ᶠ z' in 𝓝 z, z' ≠ ctr v := isOpen_compl_singleton.mem_nhds hne
    filter_upwards [hz, hne'] with z' h1 h2
    exact h1 h2
  obtain ⟨r, hr, hB, hball⟩ := exists_ball_of_eventually_pf v h1
  filter_upwards [eventually_mem_source_and_ball v hr] with w ⟨hws, hwb, hwne⟩
  by_cases hwv : w = v
  · rw [hwv]; exact meromorphicOrderAt_eq_top_iff.2 hv
  · have hz := hball _ hwb (hwne hwv)

    have hchg := rd_change ψ hws
    have hτc : ContinuousAt (φ v ∘ (φ w).symm) (ctr w) :=
      (analyticAt_transition v w (mem_extChartAt_target w)
        (by rw [extChartAt_to_inv]; exact hws)).continuousAt
    have hτ0 : (φ v ∘ (φ w).symm) (ctr w) = φ v w := by
      show φ v ((φ w).symm (ctr w)) = φ v w
      rw [extChartAt_to_inv]
    have hz' : ∀ᶠ z' in 𝓝 ((φ v ∘ (φ w).symm) (ctr w)), rd ψ v z' = 0 := by rw [hτ0]; exact hz
    apply meromorphicOrderAt_eq_top_iff.2
    apply mem_nhdsWithin_of_mem_nhds
    filter_upwards [hchg, hτc.eventually hz'] with z h1 h2
    rw [h1]
    exact h2

theorem eventually_order_eq_zero (ψ : Place ℂ F → ℂ) {v : Place ℂ F}
    (hv' : MeromorphicAt (rd ψ v) (ctr v)) (hv : ∀ᶠ z in pf v, rd ψ v z ≠ 0) :
    ∀ᶠ w in 𝓝 v, w ≠ v →
      MeromorphicAt (rd ψ w) (ctr w) ∧ meromorphicOrderAt (rd ψ w) (ctr w) = 0 := by
  obtain ⟨r, hr, hB, hball⟩ := exists_ball_of_eventually_pf v (hv.and hv'.eventually_analyticAt)
  filter_upwards [eventually_mem_source_and_ball v hr] with w ⟨hws, hwb, hwne⟩ hwv
  obtain ⟨hne0, han⟩ := hball _ hwb (hwne hwv)
  have hchg := rd_change ψ hws
  have hτ : AnalyticAt ℂ (φ v ∘ (φ w).symm) (ctr w) :=
    analyticAt_transition v w (mem_extChartAt_target w) (by rw [extChartAt_to_inv]; exact hws)
  have hτ0 : (φ v ∘ (φ w).symm) (ctr w) = φ v w := by
    show φ v ((φ w).symm (ctr w)) = φ v w
    rw [extChartAt_to_inv]
  have hcomp : AnalyticAt ℂ (rd ψ v ∘ (φ v ∘ (φ w).symm)) (ctr w) := by
    refine AnalyticAt.comp ?_ hτ
    rw [hτ0]; exact han
  have han' : AnalyticAt ℂ (rd ψ w) (ctr w) := hcomp.congr hchg.symm
  refine ⟨han'.meromorphicAt, ?_⟩
  rw [han'.meromorphicOrderAt_eq, (han'.analyticOrderAt_eq_zero).2 ?_]
  · simp
  · rw [hchg.self_of_nhds, Function.comp_apply, hτ0]
    exact hne0

variable [ConnectedSpace (Place ℂ F)]

theorem forall_order_eq_top_or (ψ : Place ℂ F → ℂ) (hψ : ∀ v, MeromorphicAt (rd ψ v) (ctr v)) :
    (∀ v, meromorphicOrderAt (rd ψ v) (ctr v) = ⊤) ∨ ∀ v, meromorphicOrderAt (rd ψ v) (ctr v) ≠ ⊤ := by
  set A : Set (Place ℂ F) := {v | meromorphicOrderAt (rd ψ v) (ctr v) = ⊤} with hA
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro v hv
    exact eventually_order_eq_top ψ (meromorphicOrderAt_eq_top_iff.1 hv)
  have hclosed : IsClosed A := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro v hv
    have hne : ∀ᶠ z in pf v, rd ψ v z ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hψ v)).1 hv
    filter_upwards [eventually_order_eq_zero ψ (hψ v) hne] with w hw
    by_cases hwv : w = v
    · rw [hwv]; exact hv
    · intro hwA
      have := (hw hwv).2
      rw [show meromorphicOrderAt (rd ψ w) (ctr w) = ⊤ from hwA] at this
      exact WithTop.top_ne_zero this
  rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with h | h
  · right
    intro v hv
    have : v ∈ A := hv
    rw [h] at this
    exact this
  · left
    intro v
    have : v ∈ A := by rw [h]; exact mem_univ v
    exact this

variable [CompactSpace (Place ℂ F)]

omit [ConnectedSpace (Place ℂ F)] in

theorem finite_setOf_order_neg (ψ : Place ℂ F → ℂ) (hψ : ∀ v, MeromorphicAt (rd ψ v) (ctr v))
    (hfin : ∀ v, meromorphicOrderAt (rd ψ v) (ctr v) ≠ ⊤) :
    {v | meromorphicOrderAt (rd ψ v) (ctr v) < 0}.Finite := by

  have hU : ∀ v : Place ℂ F, ∃ U ∈ 𝓝 v, ∀ w ∈ U, w ≠ v → meromorphicOrderAt (rd ψ w) (ctr w) = 0 := by
    intro v
    have hne : ∀ᶠ z in pf v, rd ψ v z ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hψ v)).1 (hfin v)
    exact ⟨_, eventually_order_eq_zero ψ (hψ v) hne, fun w hw hwv => (hw hwv).2⟩
  choose U hUn hUz using hU
  obtain ⟨t, -, hcover⟩ := isCompact_univ.elim_nhds_subcover U fun v _ => hUn v
  refine (t.finite_toSet).subset fun w hw => ?_
  obtain ⟨v, hv, hwU⟩ := mem_iUnion₂.1 (hcover (mem_univ w))
  by_contra hwt
  have hne : w ≠ v := fun h => hwt (h ▸ hv)
  have h0 := hUz v w hwU hne
  have hlt : meromorphicOrderAt (rd ψ w) (ctr w) < 0 := hw
  rw [h0] at hlt
  exact lt_irrefl _ hlt

end Global

section Degree

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]

theorem degree_eq_sum (D : Divisor ℂ F) : Divisor.degree D = ∑ v ∈ D.support, D v := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [IsCurveOver.deg_eq_one_of_isAlgClosed v]

theorem degree_nonneg {D : Divisor ℂ F} (hD : 0 ≤ D) : 0 ≤ Divisor.degree D := by
  rw [degree_eq_sum]
  exact Finset.sum_nonneg fun v _ => hD v

theorem le_degree {D : Divisor ℂ F} (hD : 0 ≤ D) (v : Place ℂ F) : D v ≤ Divisor.degree D := by
  rw [degree_eq_sum]
  by_cases hv : v ∈ D.support
  · exact Finset.single_le_sum (fun w _ => hD w) hv
  · rw [Finsupp.notMem_support_iff.1 hv]
    exact Finset.sum_nonneg fun w _ => hD w

end Degree

section Main

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)] [T2Space (Place ℂ F)]
variable [ConnectedSpace (Place ℂ F)]

theorem withTop_le_add3 {p m n k : ℤ} (h : p ≤ m + n + k) :
    ((p : ℤ) : WithTop ℤ) ≤ (m : WithTop ℤ) + (n : WithTop ℤ) + (k : WithTop ℤ) := by
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  exact h

theorem main
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ChartCompatible F) (g : Place ℂ F → ℂ) (hg : ∀ v, MeromorphicAt (rd g v) (ctr v)) :
    ∃ f : F, ∀ v, rd g v =ᶠ[pf v] read v f := by
  classical

  rcases forall_order_eq_top_or g hg with htop | hfin
  · refine ⟨0, fun v => ?_⟩
    rw [read_zero]
    exact meromorphicOrderAt_eq_top_iff.1 (htop v)

  have hordZ : ∀ v, ∃ m : ℤ, meromorphicOrderAt (rd g v) (ctr v) = m := fun v => by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hfin v)
    exact ⟨m, hm.symm⟩
  choose og hog using hordZ
  have hEfin : (Function.support fun v => max 0 (-og v)).Finite := by
    refine (finite_setOf_order_neg g hg hfin).subset fun v hv => ?_
    have h1 : max 0 (-og v) ≠ 0 := hv
    show meromorphicOrderAt (rd g v) (ctr v) < 0
    rw [hog v]
    have : og v < 0 := by
      by_contra hcon
      exact h1 (max_eq_left (by omega))
    exact_mod_cast this
  obtain ⟨E, hE⟩ : ∃ E : Divisor ℂ F, ∀ v, E v = max 0 (-og v) :=
    ⟨Finsupp.ofSupportFinite _ hEfin, fun v => rfl⟩
  have hE0' : ∀ v, (0 : ℤ) ≤ E v := fun v => by rw [hE]; exact le_max_left _ _
  have hE0 : 0 ≤ E := fun v => hE0' v
  have hdegE : 0 ≤ Divisor.degree E := degree_nonneg hE0

  obtain ⟨x, hx, hxfd⟩ := hfg
  haveI := hxfd
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  have hBfin : (Function.support fun v : Place ℂ F => max 0 (-v.ord x)).Finite := by
    refine (finite_setOf_ord_ne_zero (K := ℂ) hx0).subset fun v hv => ?_
    have h1 : max 0 (-v.ord x) ≠ 0 := hv
    show v.ord x ≠ 0
    intro h0
    exact h1 (by rw [h0]; simp)
  obtain ⟨B, hB⟩ : ∃ B : Divisor ℂ F, ∀ v, B v = max 0 (-v.ord x) :=
    ⟨Finsupp.ofSupportFinite _ hBfin, fun v => rfl⟩
  have hB0' : ∀ v, (0 : ℤ) ≤ B v := fun v => by rw [hB]; exact le_max_left _ _
  have hB0 : 0 ≤ B := fun v => hB0' v
  obtain ⟨hℓ0, Mℓ, -, hMℓ'⟩ := exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx B hB
  obtain ⟨γ, hγ⟩ : ∃ γ : ℕ, γ = genusFF ℂ F := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = Divisor.degree B := ⟨_, rfl⟩
  have hMℓ : ∀ N : ℕ, Mℓ ≤ N → (ell (N • B) : ℤ) = N * d + 1 - γ := by
    intro N hN; rw [hMℓ' N hN, hγ, hd]
  clear hMℓ'

  have hd1 : 1 ≤ d := by

    by_contra hlt
    have hpole : ∀ v : Place ℂ F, 0 ≤ v.ord x := by
      intro v
      by_contra hneg
      have h1 : 1 ≤ B v := by rw [hB]; omega
      exact hlt (h1.trans (hd ▸ le_degree hB0 v))
    have hxL : x ∈ LSpace (0 : Divisor ℂ F) := by
      rw [mem_riemannRochSpace_iff]
      intro v
      right
      simpa using hpole v
    have h1L : (1 : F) ∈ LSpace (0 : Divisor ℂ F) := by
      rw [mem_riemannRochSpace_iff]
      intro v
      right
      simp [v.ord_one]
    haveI : Module.Finite ℂ ↥(LSpace (0 : Divisor ℂ F)) :=
      Module.finite_of_finrank_pos (by rw [show Module.finrank ℂ _ = ell (0 : Divisor ℂ F) from rfl, hℓ0]; exact one_pos)

    have hli : LinearIndependent ℂ ![(⟨1, h1L⟩ : ↥(LSpace (0 : Divisor ℂ F))), ⟨x, hxL⟩] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hst' : algebraMap ℂ F s + t • x = 0 := by
        have := congrArg Subtype.val hst
        simpa [Algebra.smul_def] using this
      by_cases ht : t = 0
      · subst ht
        simp only [zero_smul, add_zero] at hst'
        exact ⟨(algebraMap ℂ F).injective (by rw [hst', map_zero]), rfl⟩
      · exfalso
        apply hx
        have hxeq : x = algebraMap ℂ F (-s / t) := by
          rw [map_div₀, map_neg, eq_div_iff ((map_ne_zero _).2 ht)]
          rw [Algebra.smul_def] at hst'
          linear_combination hst'
        rw [hxeq]
        exact isAlgebraic_algebraMap _
    have := hli.fintype_card_le_finrank
    rw [show Module.finrank ℂ ↥(LSpace (0 : Divisor ℂ F)) = ell (0 : Divisor ℂ F) from rfl,
      hℓ0] at this
    simp at this

  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, N₁ = Mℓ + γ + (Divisor.degree E).toNat := ⟨_, rfl⟩
  have hℓN₁ : (ell (N₁ • B) : ℤ) = N₁ * d + 1 - γ := hMℓ N₁ (by omega)
  have hN₁d : (N₁ : ℤ) ≤ N₁ * d := by nlinarith only [hd1, (Nat.cast_nonneg N₁ : (0 : ℤ) ≤ N₁)]
  have hdegEnat : ((Divisor.degree E).toNat : ℤ) = Divisor.degree E := Int.toNat_of_nonneg hdegE
  have hN₁z : (N₁ : ℤ) = Mℓ + γ + Divisor.degree E := by rw [hN₁]; push_cast; rw [hdegEnat]
  haveI : FiniteDimensional ℂ ↥(LSpace (N₁ • B)) := by
    refine Module.finite_of_finrank_pos ?_
    have : (0 : ℤ) < (ell (N₁ • B) : ℤ) := by
      rw [hℓN₁]; linarith only [hN₁d, hN₁z, hdegE, (Nat.cast_nonneg Mℓ : (0 : ℤ) ≤ Mℓ)]
    exact_mod_cast this
  have hle : N₁ • B - E ≤ N₁ • B := fun v => by
    simp only [Finsupp.coe_sub, Pi.sub_apply]
    linarith only [hE0' v]
  have hsub := ell_sub_ell_le_degree_sub_degree (K := ℂ) hle
  rw [map_sub, sub_sub_cancel] at hsub
  have hℓ1 : (1 : ℤ) ≤ (ell (N₁ • B - E) : ℤ) := by
    linarith only [hsub, hℓN₁, hN₁d, hN₁z, (Nat.cast_nonneg Mℓ : (0 : ℤ) ≤ Mℓ)]
  obtain ⟨h, hhL, hh0⟩ : ∃ h ∈ LSpace (N₁ • B - E), h ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro hbot
    have : (ell (N₁ • B - E) : ℤ) = 0 := by
      rw [show ell (N₁ • B - E) = Module.finrank ℂ ↥(LSpace (N₁ • B - E)) from rfl, hbot,
        finrank_bot]
      rfl
    omega
  have hh_ord : ∀ v, -((N₁ : ℤ) * B v - E v) ≤ v.ord h := by
    intro v
    have := ((mem_riemannRochSpace_iff.1 hhL) v).resolve_left hh0
    simpa [Finsupp.smul_apply, nsmul_eq_mul] using this

  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, N₂ = Mℓ + 2 * γ := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = N₁ + N₂ := ⟨_, rfl⟩
  have h4 : (N : ℤ) = N₁ + N₂ := by rw [hN]; push_cast; ring
  have h5 : (N₂ : ℤ) = Mℓ + 2 * γ := by rw [hN₂]; push_cast; ring
  have hℓN : (ell (N • B) : ℤ) = N * d + 1 - γ := hMℓ N (by omega)
  have hℓN' : (ell (N₂ • B) : ℤ) = N₂ * d + 1 - γ := hMℓ N₂ (by omega)
  have hNd : (N : ℤ) ≤ N * d := by nlinarith only [hd1, (Nat.cast_nonneg N : (0 : ℤ) ≤ N)]
  have hN'd : (N₂ : ℤ) ≤ N₂ * d := by nlinarith only [hd1, (Nat.cast_nonneg N₂ : (0 : ℤ) ≤ N₂)]
  haveI hfinN : FiniteDimensional ℂ ↥(LSpace (N • B)) := by
    refine Module.finite_of_finrank_pos ?_
    have : (0 : ℤ) < (ell (N • B) : ℤ) := by
      rw [hℓN]
      linarith only [hNd, h4, h5, hN₁z, hdegE, (Nat.cast_nonneg Mℓ : (0 : ℤ) ≤ Mℓ),
        (Nat.cast_nonneg γ : (0 : ℤ) ≤ γ)]
    exact_mod_cast this
  haveI hfinN' : FiniteDimensional ℂ ↥(LSpace (N₂ • B)) := by
    refine Module.finite_of_finrank_pos ?_
    have : (0 : ℤ) < (ell (N₂ • B) : ℤ) := by
      rw [hℓN']
      linarith only [hN'd, h5, (Nat.cast_nonneg Mℓ : (0 : ℤ) ≤ Mℓ), (Nat.cast_nonneg γ : (0 : ℤ) ≤ γ)]
    exact_mod_cast this
  obtain ⟨a, bf, ha⟩ : ∃ (a : ℕ) (bf : Module.Basis (Fin a) ℂ ↥(LSpace (N • B))),
      (a : ℤ) = ell (N • B) := ⟨_, Module.finBasis ℂ _, rfl⟩
  obtain ⟨b, be, hb⟩ : ∃ (b : ℕ) (be : Module.Basis (Fin b) ℂ ↥(LSpace (N₂ • B))),
      (b : ℤ) = ell (N₂ • B) := ⟨_, Module.finBasis ℂ _, rfl⟩
  let ψ : Fin a ⊕ Fin b → Place ℂ F → ℂ :=
    Sum.elim (fun i P => Place.evalAt P (bf i : F))
      (fun j P => g P * Place.evalAt P h * Place.evalAt P (be j : F))

  obtain ⟨DN, hDN, hDNsum⟩ : ∃ DN : Place ℂ F →₀ ℕ, (∀ v, (DN v : ℤ) = N * B v) ∧
      ((DN.sum fun _ n => n : ℕ) : ℤ) = N * d := by
    refine ⟨Finsupp.mapRange Int.toNat (by simp) (N • B), fun v => ?_, ?_⟩
    · rw [Finsupp.mapRange_apply, Finsupp.smul_apply, nsmul_eq_mul,
        Int.toNat_of_nonneg (mul_nonneg (by positivity) (hB0' v))]
    · rw [Finsupp.sum_mapRange_index (fun _ => rfl), Finsupp.sum, Nat.cast_sum, hd,
        show (N : ℤ) * Divisor.degree B = Divisor.degree (N • B) by rw [map_nsmul, nsmul_eq_mul],
        degree_eq_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finsupp.smul_apply, nsmul_eq_mul]
      exact Int.toNat_of_nonneg (mul_nonneg (by positivity) (hB0' v))

  have hψmero : ∀ i v, MeromorphicAt (rd (ψ i) v) (ctr v) := by
    rintro (i | j) v
    · exact meromorphicAt_read hF v _
    · show MeromorphicAt (rd g v * read v h * read v (be j : F)) (ctr v)
      exact ((hg v).mul (meromorphicAt_read hF v h)).mul (meromorphicAt_read hF v _)
  have hψord : ∀ i v, ((-(DN v : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (rd (ψ i) v) (ctr v) := by
    rintro (i | j) v
    · show ((-(DN v : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (read v (bf i : F)) (ctr v)
      have htop0 : meromorphicOrderAt (0 : ℂ → ℂ) (ctr v) = ⊤ :=
        meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ => rfl)
      by_cases h0 : (bf i : F) = 0
      · rw [h0, read_zero, htop0]
        exact le_top
      · rw [meromorphicOrderAt_read hF v h0, WithTop.coe_le_coe, hDN]
        have := ((mem_riemannRochSpace_iff.1 (bf i).2) v).resolve_left h0
        simpa [Finsupp.smul_apply, nsmul_eq_mul] using this
    · show ((-(DN v : ℤ) : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (rd g v * read v h * read v (be j : F)) (ctr v)
      have htop0 : meromorphicOrderAt (0 : ℂ → ℂ) (ctr v) = ⊤ :=
        meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ => rfl)
      by_cases h0 : (be j : F) = 0
      · have : rd g v * read v h * read v (be j : F) = 0 := by
          rw [h0, read_zero, mul_zero]
        rw [this, htop0]
        exact le_top
      · have hm1 : MeromorphicAt (rd g v * read v h) (ctr v) := (hg v).mul (meromorphicAt_read hF v h)
        have e1 := meromorphicOrderAt_mul hm1 (meromorphicAt_read hF v (be j : F))
        have e2 := meromorphicOrderAt_mul (hg v) (meromorphicAt_read hF v h)
        rw [e1, e2, hog v, meromorphicOrderAt_read hF v hh0, meromorphicOrderAt_read hF v h0, hDN]
        apply withTop_le_add3
        have h1 : -E v ≤ og v := by rw [hE]; exact neg_le.1 (le_max_right _ _)
        have h2 := hh_ord v
        have h3 : -((N₂ : ℤ) * B v) ≤ v.ord (be j : F) := by
          have := ((mem_riemannRochSpace_iff.1 (be j).2) v).resolve_left h0
          simpa [Finsupp.smul_apply, nsmul_eq_mul] using this
        rw [h4, add_mul]
        linarith only [h1, h2, h3]
  have hcard : (DN.sum fun _ n => n) + 1 < Fintype.card (Fin a ⊕ Fin b) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have key : ((DN.sum fun _ n => n : ℕ) : ℤ) + 1 < (a : ℤ) + b := by
      rw [hDNsum, ha, hb, hℓN, hℓN']
      linarith only [hN'd, h5, (Nat.cast_nonneg Mℓ : (0 : ℤ) ≤ Mℓ), (Nat.cast_nonneg γ : (0 : ℤ) ≤ γ)]
    exact_mod_cast key
  obtain ⟨c, hc0, hc⟩ :=
    Manifold.exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card DN ψ hψmero hψord hcard

  set wF : F := ∑ i, c (Sum.inl i) • (bf i : F) with hwF_def
  set uF : F := ∑ j, c (Sum.inr j) • (be j : F) with huF_def
  have hrel : ∀ v, ∀ᶠ z in pf v, read v wF z + rd g v z * read v h z * read v uF z = 0 := by
    intro v
    filter_upwards [hc v, read_sum Finset.univ v (fun i => c (Sum.inl i)) (fun i => (bf i : F)),
      read_sum Finset.univ v (fun j => c (Sum.inr j)) (fun j => (be j : F))] with z hz hw hu
    rw [hw, hu, Finset.mul_sum]
    simp only [Pi.zero_apply, Fintype.sum_sum_type] at hz
    rw [← hz]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ψ, rd, read, Sum.elim_inr]
    ring
  by_cases huF : uF = 0
  ·
    exfalso
    have hinr : ∀ j, c (Sum.inr j) = 0 := by
      have hli := be.linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      refine hli (fun j => c (Sum.inr j)) ?_
      rw [← Submodule.coe_eq_zero, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact huF
    have hwF : wF = 0 := by
      obtain ⟨v⟩ := (inferInstance : Nonempty (Place ℂ F))
      apply eq_zero_of_read_eventuallyEq_zero hF v
      filter_upwards [hrel v] with z hz
      rw [huF, read_zero, Pi.zero_apply, mul_zero, add_zero] at hz
      exact hz
    have hinl : ∀ i, c (Sum.inl i) = 0 := by
      have hli := bf.linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      refine hli (fun i => c (Sum.inl i)) ?_
      rw [← Submodule.coe_eq_zero, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hwF
    apply hc0
    funext i
    rcases i with i | j
    · exact hinl i
    · exact hinr j
  ·
    refine ⟨-wF * (h * uF)⁻¹, fun v => ?_⟩
    filter_upwards [hrel v, read_mul v (-wF) (h * uF)⁻¹, read_neg v wF,
      read_inv v (mul_ne_zero hh0 huF), read_mul v h uF, read_ne_zero v hh0, read_ne_zero v huF]
      with z hz h1 h2 h3 h4 h5 h6
    rw [h1, Pi.mul_apply, h2, Pi.neg_apply, h3, Pi.inv_apply, h4, Pi.mul_apply]
    field_simp
    linear_combination hz

end Main

end AlgebraicCurve.GAGAProof

open AlgebraicCurve.GAGAProof in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (g : Place ℂ F → ℂ)
    (hg : ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v)) :
    ∃ f : F, ∀ v : Place ℂ F,
      (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v)]
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) :=
  main hfg hF g hg

end
end S_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt
end P2MW
export P2MW.S_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt (solution)
