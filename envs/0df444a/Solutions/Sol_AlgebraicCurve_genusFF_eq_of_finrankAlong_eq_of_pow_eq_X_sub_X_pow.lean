-- Prove2me | solution 1 for AlgebraicCurve.genusFF_eq_of_finrankAlong_eq_of_pow_eq_X_sub_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/37ac028d-a382-549c-9150-3a3d6602d585

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_finsum_ramificationIndex_ratFunc_sub_one_eq_of_tame
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors
import Theorems.Thm_AlgebraicCurve_instIsCurveOverRatFunc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_genusFF_eq_of_finrankAlong_eq_of_pow_eq_X_sub_X_pow
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

namespace KummerEngine

p2m_open "AlgebraicCurve~genus AlgebraicCurve.RationalFunctionField~placeOfPoint_ne_placeInfty Polynomial"
open scoped Classical

set_option linter.unusedSectionVars false

section Generic

theorem card_fiber_eq_one_of_forall_ramificationIndex_eq
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w)
    (he : ∀ w ∈ v.fiber F', w.ramificationIndex F = Module.finrank F F') :
    (v.fiber F').card = 1 := by
  have hsum := AlgebraicCurve.Place.sum_ramificationIndex_eq_finrank v hv hrat
  have hsum' : ∑ w ∈ v.fiber F', (Module.finrank F F' : ℤ) = Module.finrank F F' :=
    (Finset.sum_congr rfl fun w hw => by rw [he w hw]).trans hsum
  rw [Finset.sum_const, nsmul_eq_mul] at hsum'
  have hpos : (0 : ℤ) < Module.finrank F F' := by exact_mod_cast Module.finrank_pos
  have hcard : ((v.fiber F').card : ℤ) = 1 := Int.eq_one_of_mul_eq_self_left hpos.ne' hsum'
  exact_mod_cast hcard

theorem finsum_eq_sum_sum_fiber
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']
    (S : Finset (Place K F)) (g : Place K F' → ℤ) (hg : ∀ w, w.restrict F ∉ S → g w = 0) :
    ∑ᶠ w, g w = ∑ v ∈ S, ∑ w ∈ v.fiber F', g w := by
  classical
  have hsupp : Function.support g ⊆ ↑(S.biUnion fun v => v.fiber F') := by
    intro w hw
    rw [Function.mem_support] at hw
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨w.restrict F, ?_, Place.restrict_mem_fiber w⟩
    by_contra h
    exact hw (hg w h)
  rw [finsum_eq_sum_of_support_subset g hsupp, Finset.sum_biUnion]
  intro v₁ _ v₂ _ hne
  show Disjoint (v₁.fiber F') (v₂.fiber F')
  rw [Finset.disjoint_left]
  intro w h1 h2
  exact hne ((Place.mem_fiber.mp h1).symm.trans (Place.mem_fiber.mp h2))

end Generic

section Radicand

variable {k : Type*} [Field k] [IsAlgClosed k] (q : ℕ) [hq : Fact q.Prime] [CharP k q]

noncomputable def P0 (k : Type*) [Field k] (q : ℕ) : k[X] := X - X ^ q

theorem one_lt_q : 1 < q := hq.out.one_lt

theorem natDegree_P0 : (P0 k q).natDegree = q := by
  have h1 : 1 < q := one_lt_q q
  rw [P0, natDegree_sub_eq_right_of_natDegree_lt] <;> simp [h1]

theorem P0_ne_zero : P0 k q ≠ 0 := by
  intro h
  have h1 := natDegree_P0 (k := k) q
  have h2 := one_lt_q q
  rw [h, natDegree_zero] at h1
  omega

theorem derivative_P0 : derivative (P0 k q) = 1 := by
  rw [P0, derivative_sub, derivative_X, derivative_X_pow, CharP.cast_eq_zero k q, C_0, zero_mul, sub_zero]

theorem separable_P0 : (P0 k q).Separable := by
  rw [Polynomial.separable_def, derivative_P0]
  exact isCoprime_one_right

theorem rootMultiplicity_P0_le_one (a : k) : rootMultiplicity a (P0 k q) ≤ 1 := by
  rw [← count_roots]
  exact count_roots_le_one (separable_P0 q) a

theorem rootMultiplicity_P0_of_isRoot {a : k} (ha : (P0 k q).IsRoot a) : rootMultiplicity a (P0 k q) = 1 :=
  le_antisymm (rootMultiplicity_P0_le_one q a) ((rootMultiplicity_pos (P0_ne_zero q)).mpr ha)

theorem rootMultiplicity_P0_of_not_isRoot {a : k} (ha : ¬ (P0 k q).IsRoot a) : rootMultiplicity a (P0 k q) = 0 :=
  rootMultiplicity_eq_zero ha

theorem card_roots_P0 : (P0 k q).roots.toFinset.card = q := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots (separable_P0 q)),
    ← (IsAlgClosed.splits (P0 k q)).natDegree_eq_card_roots, natDegree_P0]

noncomputable def u0 (k : Type*) [Field k] (q : ℕ) : RatFunc k := algebraMap k[X] (RatFunc k) (P0 k q)

theorem u0_eq : u0 k q = RatFunc.X - RatFunc.X ^ q := by
  rw [u0, P0, map_sub, map_pow, RatFunc.algebraMap_X]

theorem u0_ne_zero : u0 k q ≠ 0 := by
  rw [u0]
  exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr (P0_ne_zero q)

theorem ord_placeOfPoint_u0 (a : k) :
    (placeOfPoint k a).ord (u0 k q) = rootMultiplicity a (P0 k q) :=
  ord_placeOfPoint_algebraMap a (P0_ne_zero q)

theorem ord_placeInfty_u0 : (placeInfty k).ord (u0 k q) = -(q : ℤ) := by
  rw [u0, ord_placeInfty_algebraMap (P0_ne_zero q), natDegree_P0]

omit [IsAlgClosed k] hq [CharP k q] in
theorem placeOfPoint_ne_placeInfty (a : k) : placeOfPoint k a ≠ placeInfty k := by
  intro h
  have h1 := ord_placeOfPoint_algebraMap (K := k) a (X_ne_zero (R := k))
  have h2 := ord_placeInfty_algebraMap (K := k) (X_ne_zero (R := k))
  rw [h, h2, natDegree_X] at h1
  have : (0 : ℤ) ≤ rootMultiplicity a (X : k[X]) := by positivity
  omega

noncomputable def S (k : Type*) [Field k] (q : ℕ) : Finset (Place k (RatFunc k)) :=
  insert (placeInfty k) ((P0 k q).roots.toFinset.image (placeOfPoint k))

theorem card_S : (S k q).card = q + 1 := by
  rw [S, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (placeOfPoint_injective k), card_roots_P0]
  simp only [Finset.mem_image, Multiset.mem_toFinset, not_exists, not_and]
  intro a _ h
  exact placeOfPoint_ne_placeInfty a h

omit [IsAlgClosed k] hq [CharP k q] in
theorem placeInfty_mem_S : placeInfty k ∈ S k q := Finset.mem_insert_self _ _

theorem placeOfPoint_mem_S_iff (a : k) : placeOfPoint k a ∈ S k q ↔ (P0 k q).IsRoot a := by
  rw [S, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨b, hb, hba⟩)
    · exact absurd h (placeOfPoint_ne_placeInfty a)
    · rw [placeOfPoint_injective k hba] at hb
      exact (mem_roots (P0_ne_zero q)).mp (Multiset.mem_toFinset.mp hb)
  · intro h
    exact Or.inr ⟨a, Multiset.mem_toFinset.mpr ((mem_roots (P0_ne_zero q)).mpr h), rfl⟩

end Radicand

section Engine

theorem genusFF_eq_of_pow_eq_X_sub_X_pow
    {k : Type*} [Field k] [IsAlgClosed k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (n : ℕ) (hn : (n : k) ≠ 0) (hqn : q.Coprime n)
    {E : Type*} [Field E] [Algebra k E] (φ : RatFunc k →ₐ[k] E)
    (hfin : FiniteAlong k φ) (hsep : SeparableAlong k φ) (hdeg : finrankAlong k φ = n)
    (c : E) (hc : φ (RatFunc.X - RatFunc.X ^ q) = c ^ n)
    (hgen : Subfield.closure (Set.range φ ∪ {c}) = ⊤) :
    genusFF k E = (n - 1) * (q - 1) / 2 := by
  classical
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : FiniteDimensional (RatFunc k) E := hfin
  haveI : Algebra.IsSeparable (RatFunc k) E := hsep
  haveI : HasPrincipalDivisors k (RatFunc k) := (instIsCurveOverRatFunc k).toHasPrincipalDivisors
  haveI : HasPrincipalDivisors k E :=
    hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors k (RatFunc k) E
  have hφ : φ.toRingHom.IsIntegral := fun z => (Algebra.IsIntegral.isIntegral (R := RatFunc k) z)
  have hdeg' : Module.finrank (RatFunc k) E = n := hdeg
  have hn0 : 0 < n := by rw [← hdeg']; exact Module.finrank_pos
  have hcu : φ (u0 k q) = c ^ n := by rw [u0_eq]; exact hc

  have he_mem : ∀ w : Place k E, w.restrict (RatFunc k) ∈ S k q → w.ramificationIndex (RatFunc k) = n := by
    intro w hw
    refine Place.ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord φ hφ hfin hsep n hdeg c (u0 k q) hcu w ?_
    change IsCoprime ((w.restrict (RatFunc k)).ord (u0 k q)) _
    rcases eq_placeOfPoint_or_eq_placeInfty k (w.restrict (RatFunc k)) with ⟨a, ha⟩ | h
    · rw [ha] at hw ⊢
      rw [ord_placeOfPoint_u0, rootMultiplicity_P0_of_isRoot q ((placeOfPoint_mem_S_iff q a).mp hw)]
      exact isCoprime_one_left
    · rw [h, ord_placeInfty_u0]
      exact (Nat.isCoprime_iff_coprime.mpr hqn).neg_left

  have he_not : ∀ w : Place k E, w.restrict (RatFunc k) ∉ S k q → w.ramificationIndex (RatFunc k) = 1 := by
    intro w hw
    have hrat : (w.restrict (RatFunc k)).IsRational := Place.isRational_of_isAlgClosed _
    rcases eq_placeOfPoint_or_eq_placeInfty k (w.restrict (RatFunc k)) with ⟨a, ha⟩ | h
    · have hroot : ¬ (P0 k q).IsRoot a := fun hr => hw (ha ▸ (placeOfPoint_mem_S_iff q a).mpr hr)
      have hord : (w.restrict (RatFunc k)).ord (u0 k q) = 0 := by
        rw [ha, ord_placeOfPoint_u0, rootMultiplicity_P0_of_not_isRoot q hroot, Nat.cast_zero]
      have hmem : u0 k q ∈ (w.restrict (RatFunc k)).toValuationSubring ∧
          (u0 k q)⁻¹ ∈ (w.restrict (RatFunc k)).toValuationSubring := by
        constructor
        · exact (Place.mem_iff_ord_nonneg _ (u0_ne_zero q)).mpr (by rw [hord])
        · exact (Place.mem_iff_ord_nonneg _ (inv_ne_zero (u0_ne_zero q))).mpr
            (by rw [Place.ord_inv, hord, neg_zero])
      exact Place.ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem φ hφ n hn c hgen (u0 k q) hcu w
        hrat hmem
    · exact absurd (h ▸ placeInfty_mem_S (k := k) (q := q)) hw

  have htame : ∀ w : Place k E, ((w.ramificationIndex (RatFunc k) : ℕ) : k) ≠ 0 := by
    intro w
    by_cases hw : w.restrict (RatFunc k) ∈ S k q
    · rw [he_mem w hw]; exact hn
    · rw [he_not w hw, Nat.cast_one]; exact one_ne_zero

  have hcard : ∀ v ∈ S k q, (v.fiber E).card = 1 := by
    intro v hv
    refine card_fiber_eq_one_of_forall_ramificationIndex_eq v (Place.isRational_of_isAlgClosed _)
      (fun w _ => Place.isRational_of_isAlgClosed _) (fun w hw => ?_)
    rw [hdeg']
    exact he_mem w ((Place.mem_fiber.mp hw).symm ▸ hv)

  have hcount : ∑ᶠ w : Place k E, ((w.ramificationIndex (RatFunc k) : ℤ) - 1) = (q + 1) * (n - 1 : ℤ) := by
    rw [finsum_eq_sum_sum_fiber (S k q) _ (fun w hw => by rw [he_not w hw]; simp)]
    have h : ∀ v ∈ S k q, ∑ w ∈ v.fiber E, ((w.ramificationIndex (RatFunc k) : ℤ) - 1) = (n - 1 : ℤ) := by
      intro v hv
      rw [Finset.sum_congr rfl (fun w hw => by rw [he_mem w ((Place.mem_fiber.mp hw).symm ▸ hv)])]
      rw [Finset.sum_const, hcard v hv]
      simp
    rw [Finset.sum_congr rfl h, Finset.sum_const, card_S]
    push_cast
    ring

  have hRH := finsum_ramificationIndex_ratFunc_sub_one_eq_of_tame (K := k) (F := E) htame
  rw [hcount, hdeg'] at hRH

  have h1 : 1 ≤ q := (one_lt_q q).le
  have h2 : 2 * (genusFF k E : ℤ) = (n - 1 : ℤ) * (q - 1 : ℤ) := by linear_combination (-1 : ℤ) * hRH
  have h3 : 2 * genusFF k E = (n - 1) * (q - 1) := by
    zify [h1, hn0]
    linear_combination h2
  symm
  apply Nat.div_eq_of_eq_mul_left two_pos
  rw [Nat.mul_comm _ 2]
  exact h3.symm

end Engine

end KummerEngine

theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (n : ℕ) (hn : (n : k) ≠ 0) (hqn : q.Coprime n)
    {E : Type*} [Field E] [Algebra k E] (φ : RatFunc k →ₐ[k] E)
    (hfin : AlgebraicCurve.FiniteAlong k φ) (hsep : AlgebraicCurve.SeparableAlong k φ)
    (hdeg : AlgebraicCurve.finrankAlong k φ = n)
    (c : E) (hc : φ (RatFunc.X - RatFunc.X ^ q) = c ^ n)
    (hgen : Subfield.closure (Set.range φ ∪ {c}) = ⊤) :
    AlgebraicCurve.genusFF k E = (n - 1) * (q - 1) / 2 :=
  KummerEngine.genusFF_eq_of_pow_eq_X_sub_X_pow q n hn hqn φ hfin hsep hdeg c hc hgen

end S_AlgebraicCurve_genusFF_eq_of_finrankAlong_eq_of_pow_eq_X_sub_X_pow
end P2MW
export P2MW.S_AlgebraicCurve_genusFF_eq_of_finrankAlong_eq_of_pow_eq_X_sub_X_pow (solution)
