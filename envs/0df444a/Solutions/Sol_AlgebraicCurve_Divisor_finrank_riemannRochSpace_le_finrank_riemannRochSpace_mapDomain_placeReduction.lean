-- Prove2me | solution 1 for AlgebraicCurve.Divisor.finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/fede05e7-bf62-5f0a-a7a1-84585f93b5d5

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_exists_regularProlongation_retraction_of_constantField_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank
import Theorems.Thm_AlgebraicCurve_Divisor_mapDomain_placeReduction_eq_ord_of_retraction
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

p2m_open "AlgebraicCurve~linearIndependent_pow_of_transcendental"
open scoped IntermediateField.algebraAdjoinAdjoin

namespace DeuringLowerSemicontinuity

section RationalPlace

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
  (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)

include hKA in
theorem valuation_algebraMap_eq_one {k : K} (hk : k ≠ 0) :
    A.valuation (algebraMap K E k) = 1 := by
  apply le_antisymm ((A.valuation_le_one_iff _).mpr (hKA k))
  have h1 : A.valuation (algebraMap K E k) * A.valuation (algebraMap K E k⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hk, map_one, map_one]
  have h2 : A.valuation (algebraMap K E k⁻¹) ≤ 1 := (A.valuation_le_one_iff _).mpr (hKA _)
  calc (1 : A.ValueGroup) = _ := h1.symm
    _ ≤ A.valuation (algebraMap K E k) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

include hKA in
theorem valuation_algebraMap_le_one (k : K) : A.valuation (algebraMap K E k) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (hKA k)

include hKA in

theorem const_unique {a : E} {k k' : K}
    (hk : A.valuation (a - algebraMap K E k) < 1) (hk' : A.valuation (a - algebraMap K E k') < 1) :
    k = k' := by
  by_contra hne
  have hsub : algebraMap K E k' - algebraMap K E k =
      (a - algebraMap K E k) - (a - algebraMap K E k') := by ring
  have h1 : A.valuation (algebraMap K E k' - algebraMap K E k) < 1 := by
    rw [hsub]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hk hk')
  have h2 : A.valuation (algebraMap K E k' - algebraMap K E k) = 1 := by
    rw [← map_sub]
    exact valuation_algebraMap_eq_one A hKA (sub_ne_zero.mpr (Ne.symm hne))
  exact (lt_irrefl (1 : A.ValueGroup)) (h2 ▸ h1)

noncomputable def sigmaFun (a : A) : K := (hArat a a.2).choose

theorem sigmaFun_spec (a : A) :
    A.valuation ((a : E) - algebraMap K E (sigmaFun A hArat a)) < 1 :=
  (hArat a a.2).choose_spec

include hKA in
theorem sigmaFun_eq_iff (a : A) (k : K) :
    sigmaFun A hArat a = k ↔ A.valuation ((a : E) - algebraMap K E k) < 1 :=
  ⟨fun h => h ▸ sigmaFun_spec A hArat a, fun h => const_unique A hKA (sigmaFun_spec A hArat a) h⟩

noncomputable def sigma : A →+* K where
  toFun := sigmaFun A hArat
  map_one' := by
    rw [sigmaFun_eq_iff A hKA hArat]
    simp
  map_mul' a b := by
    rw [sigmaFun_eq_iff A hKA hArat]
    have ha := sigmaFun_spec A hArat a
    have hb := sigmaFun_spec A hArat b
    set k := sigmaFun A hArat a
    set k' := sigmaFun A hArat b
    have hid : ((a * b : A) : E) - algebraMap K E (k * k') =
        (a : E) * ((b : E) - algebraMap K E k') + algebraMap K E k' * ((a : E) - algebraMap K E k) := by
      simp only [MulMemClass.coe_mul, map_mul]; ring
    rw [hid]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact (mul_le_mul_left (A.valuation_le_one a) _).trans_lt (by rwa [one_mul])
    · rw [map_mul]
      exact (mul_le_mul_left (valuation_algebraMap_le_one A hKA k') _).trans_lt
        (by rwa [one_mul])
  map_zero' := by
    rw [sigmaFun_eq_iff A hKA hArat]
    simp
  map_add' a b := by
    rw [sigmaFun_eq_iff A hKA hArat]
    have ha := sigmaFun_spec A hArat a
    have hb := sigmaFun_spec A hArat b
    set k := sigmaFun A hArat a
    set k' := sigmaFun A hArat b
    have hid : ((a + b : A) : E) - algebraMap K E (k + k') =
        ((a : E) - algebraMap K E k) + ((b : E) - algebraMap K E k') := by
      simp only [AddMemClass.coe_add, map_add]; ring
    rw [hid]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)

theorem sigma_apply (a : A) : sigma A hKA hArat a = sigmaFun A hArat a := rfl

theorem sigma_spec (a : A) :
    A.valuation ((a : E) - algebraMap K E (sigma A hKA hArat a)) < 1 :=
  sigmaFun_spec A hArat a

theorem sigma_eq_iff (a : A) (k : K) :
    sigma A hKA hArat a = k ↔ A.valuation ((a : E) - algebraMap K E k) < 1 :=
  sigmaFun_eq_iff A hKA hArat a k

theorem ker_sigma : RingHom.ker (sigma A hKA hArat) = IsLocalRing.maximalIdeal A := by
  ext a
  rw [RingHom.mem_ker, ValuationSubring.valuation_lt_one_iff, sigma_eq_iff, map_zero, sub_zero]

theorem sigma_algebraMap (k : K) : sigma A hKA hArat ⟨algebraMap K E k, hKA k⟩ = k := by
  rw [sigma_eq_iff]
  simp

theorem sigma_surjective : Function.Surjective (sigma A hKA hArat) :=
  fun k => ⟨⟨algebraMap K E k, hKA k⟩, sigma_algebraMap A hKA hArat k⟩

end RationalPlace

open Module

open Polynomial in

theorem linearIndependent_adjoin_simple_of_pow_mul {K' L : Type*} [Field K'] [Field L]
    [Algebra K' L] (x : L) {ι : Type*} (u : ι → L)
    (h : LinearIndependent K' fun p : ℕ × ι => x ^ p.1 * u p.2) :
    LinearIndependent (IntermediateField.adjoin K' ({x} : Set L)) u := by
  classical
  have hR : LinearIndependent (Algebra.adjoin K' ({x} : Set L)) u := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hp : ∀ i, ∃ p : K'[X], ((g i : Algebra.adjoin K' ({x} : Set L)) : L) = aeval x p := by
      intro i
      have hmem : ((g i : Algebra.adjoin K' ({x} : Set L)) : L) ∈
          (aeval (R := K') x).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (g i).2
      obtain ⟨p, hp⟩ := hmem
      exact ⟨p, hp.symm⟩
    choose p hp using hp
    set D : ℕ := (s.sup fun i => (p i).natDegree) + 1 with hD
    have hdeg : ∀ i ∈ s, (p i).natDegree < D := fun i hi =>
      Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (p i).natDegree) hi)
    rw [linearIndependent_iff'] at h
    have key := h (Finset.range D ×ˢ s) (fun q => (p q.2).coeff q.1) ?_
    · have hpi : p i = 0 := by
        ext k
        by_cases hk : k < D
        · simpa using key (k, i) (Finset.mk_mem_product (Finset.mem_range.mpr hk) hi)
        · rw [coeff_zero]
          exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i hi) (not_lt.mp hk))
      apply Subtype.ext
      rw [hp i, hpi, map_zero]; rfl
    · rw [Finset.sum_product_right]
      rw [← hg]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Subalgebra.smul_def, hp j, aeval_eq_sum_range' (hdeg j hj), Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [smul_eq_mul, smul_mul_assoc]
  exact hR.localization (IntermediateField.adjoin K' ({x} : Set L))
    (nonZeroDivisors (Algebra.adjoin K' ({x} : Set L)))

open Polynomial in

theorem linearIndependent_pow_of_transcendental {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {x : A} (hx : Transcendental R x) : LinearIndependent R fun k : ℕ => x ^ k := by
  rw [linearIndependent_iff]
  intro l hl
  have h1 : aeval x (Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff l)) =
      Finsupp.linearCombination R (fun k : ℕ => x ^ k) l := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum, Finsupp.linearCombination_apply, Finsupp.sum,
      support_ofFinsupp, AddMonoidAlgebra.coeff_ofCoeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_ofFinsupp, AddMonoidAlgebra.coeff_ofCoeff, Algebra.smul_def]
  have h2 := (transcendental_iff.mp hx) (Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff l)) (h1.trans hl)
  exact AddMonoidAlgebra.ofCoeff_injective (Polynomial.ofFinsupp_eq_zero.mp h2)

theorem algebraMap_mem_adjoin_simple {K A K' B : Type*} [Field K] [Field A] [Field K'] [Field B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra K' B] [Algebra K K'] [IsScalarTower K K' B] (x : A)
    {e : A} (he : e ∈ IntermediateField.adjoin K ({x} : Set A)) :
    algebraMap A B e ∈ IntermediateField.adjoin K' ({algebraMap A B x} : Set B) := by
  have hle : (IntermediateField.adjoin K ({x} : Set A)).map (IsScalarTower.toAlgHom K A B) ≤
      (IntermediateField.adjoin K' ({algebraMap A B x} : Set B)).restrictScalars K := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact IntermediateField.mem_adjoin_simple_self K' (algebraMap A B x)
  exact hle ⟨e, he, rfl⟩

section Degree

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem finrank_adjoin_algebraMap_eq [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {x : F} (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    finrank (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F' =
      finrank (IntermediateField.adjoin K ({x} : Set F)) F := by
  classical
  haveI := hfin
  set E : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hE
  set x' : F' := algebraMap F F' x with hx'
  set E' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hE'
  set m := finrank E F with hm_def
  let bF := Module.finBasis E F

  let xE : E := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hxEt : Transcendental K xE := by
    have : Function.Injective (algebraMap E F) := (algebraMap E F).injective
    rw [← transcendental_algebraMap_iff this]
    exact hx
  have hpow : LinearIndependent K fun k : ℕ => xE ^ k := linearIndependent_pow_of_transcendental hxEt
  have h1 : LinearIndependent K fun q : ℕ × Fin m => (xE ^ q.1 • bF q.2 : F) :=
    linearIndependent_smul hpow bF.linearIndependent

  have hW := AlgebraicCurve.linearIndependent_of_constantFieldExtension K F K' F' hfg hfg' hgen h1
  have hW' : LinearIndependent K' fun p : ℕ × Fin m => x' ^ p.1 * algebraMap F F' (bF p.2) := by
    convert hW using 1
    funext p
    simp only [hx', IntermediateField.algebraMap_apply, Algebra.smul_def, map_mul, map_pow, xE]

  set b' : Fin m → F' := fun i => algebraMap F F' (bF i) with hb'
  have hu : LinearIndependent E' b' := linearIndependent_adjoin_simple_of_pow_mul x' b' hW'

  set V : Submodule E' F' := Submodule.span E' (Set.range b') with hV_def
  have hEE' : ∀ e : E, algebraMap F F' (e : F) ∈ E' := fun e =>
    algebraMap_mem_adjoin_simple (K' := K') x e.2
  have hFV : ∀ f : F, algebraMap F F' f ∈ V := by
    intro f
    rw [← bF.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap F F' (bF.repr f i • bF i) =
        (⟨algebraMap F F' (bF.repr f i : F), hEE' _⟩ : E') • b' i := by
      rw [IntermediateField.smul_def, IntermediateField.smul_def, smul_eq_mul, map_mul,
        smul_eq_mul]
    rw [this]
    exact V.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hVV : V * V ≤ V := by
    rw [hV_def, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show b' i * b' j ∈ V
    rw [hb']; dsimp only; rw [← map_mul]; exact hFV _
  have h1V : (1 : F') ∈ V := by simpa using hFV 1
  let A : Subalgebra E' F' :=
    { carrier := V
      mul_mem' := fun ha hb => hVV (Submodule.mul_mem_mul ha hb)
      one_mem' := h1V
      add_mem' := fun ha hb => V.add_mem ha hb
      zero_mem' := V.zero_mem
      algebraMap_mem' := fun e' => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact V.smul_mem _ h1V }
  have hAfg : (Subalgebra.toSubmodule A).FG := Submodule.fg_span (Set.finite_range b')
  have hinv : ∀ z ∈ A, z⁻¹ ∈ A := fun z hz =>
    A.inv_mem_of_algebraic (x := ⟨z, hz⟩) (IsIntegral.of_mem_of_fg A hAfg z hz).isAlgebraic
  let IF : IntermediateField K' F' := (A.restrictScalars K').toIntermediateField hinv
  have hIF : IF = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨f, rfl⟩
    exact hFV f
  have hVtop : V = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IF := hIF ▸ IntermediateField.mem_top
    exact hz
  haveI : Module.Finite E' F' := ⟨hVtop ▸ Submodule.fg_span (Set.finite_range b')⟩
  have hle : Module.finrank E' F' ≤ m := by
    have := finrank_range_le_card (R := E') b'
    unfold Set.finrank at this
    rw [← hV_def, hVtop, finrank_top, Fintype.card_fin] at this
    exact this

  refine le_antisymm hle ?_
  simpa using hu.fintype_card_le_finrank

end Degree

theorem transfer_fg {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L]
    [Algebra k L] [IsScalarTower k K L] (hk : Function.Surjective (algebraMap k K))
    {x : L} (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L) :
    Transcendental k x ∧ FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L ∧
      Module.finrank (IntermediateField.adjoin k ({x} : Set L)) L =
        Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L := by
  have hxk : Transcendental k x := hx.restrictScalars (algebraMap k K).injective
  have hrange : Set.range (algebraMap k L) = Set.range (algebraMap K L) := by
    rw [IsScalarTower.algebraMap_eq k K L, RingHom.coe_comp, Set.range_comp, hk.range_eq,
      Set.image_univ]
  have hmem : ∀ y : L, y ∈ IntermediateField.adjoin k ({x} : Set L) ↔
      y ∈ IntermediateField.adjoin K ({x} : Set L) := fun y => by
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield, hrange,
      ← IntermediateField.adjoin_toSubfield, IntermediateField.mem_toSubfield]
  let j : IntermediateField.adjoin k ({x} : Set L) ≃+* IntermediateField.adjoin K ({x} : Set L) :=
    { toFun := fun y => ⟨y, (hmem y).mp y.2⟩
      invFun := fun y => ⟨y, (hmem y).mpr y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hc : (algebraMap (IntermediateField.adjoin K ({x} : Set L)) L).comp j.toRingHom =
      (RingEquiv.refl L).toRingHom.comp
        (algebraMap (IntermediateField.adjoin k ({x} : Set L)) L) :=
    RingHom.ext fun _ => rfl
  haveI := hfin
  refine ⟨hxk, ?_, Algebra.finrank_eq_of_equiv_equiv j (RingEquiv.refl L) hc⟩
  exact Module.Finite.of_equiv_equiv j.symm (RingEquiv.refl L) (RingHom.ext fun _ => rfl)

theorem finrank_eq_of_bijective_algebraMap {k K M : Type*} [CommRing k] [CommRing K]
    [AddCommGroup M] [Algebra k K] [Module K M] [Module k M] [IsScalarTower k K M]
    (hk : Function.Bijective (algebraMap k K)) : Module.finrank k M = Module.finrank K M := by
  have h := congr_arg Cardinal.toNat
    (lift_rank_eq_of_equiv_equiv (algebraMap k K) (AddEquiv.refl M) hk
      (fun r m => (algebraMap_smul K r m).symm))
  simp only [Cardinal.toNat_lift] at h
  exact h

theorem mapDomain_nonneg {α β : Type*} (r : α → β) {G : α →₀ ℤ} (hG : ∀ a, 0 ≤ G a) (b : β) :
    0 ≤ Finsupp.mapDomain r G b := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun a _ => ?_
  show 0 ≤ Finsupp.single (r a) (G a) b
  rw [Finsupp.single_apply]
  split_ifs
  · exact hG a
  · exact le_rfl

theorem main
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE)
    (A : ValuationSubring E) (r : Place E FE → Place K F)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) :
    Module.finrank E (riemannRochSpace D) ≤
      Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) := by
  classical

  by_cases hfinD : FiniteDimensional E (riemannRochSpace D)
  swap
  · rw [Module.finrank_of_not_finite hfinD]; exact Nat.zero_le _
  obtain ⟨x₀, hx₀, hfin₀⟩ := id hfg

  have hP : Nonempty (Place E FE) := by
    by_contra hno
    rw [not_nonempty_iff] at hno
    have htop : riemannRochSpace D = ⊤ :=
      eq_top_iff.mpr fun f _ => mem_riemannRochSpace_iff.mpr fun v => (IsEmpty.false v).elim
    obtain ⟨y, hy, -⟩ := hfgE
    have hT : FiniteDimensional E (⊤ : Submodule E FE) := htop ▸ hfinD
    haveI : FiniteDimensional E FE := LinearEquiv.finiteDimensional (Submodule.topEquiv)
    exact hy (Algebra.IsAlgebraic.isAlgebraic (R := E) y)
  obtain ⟨P₀⟩ := hP

  haveI hL0 : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F
      (AlgebraicCurve.constantsAreBase_of_deg_eq_one (r P₀)
        (IsCurveOver.deg_eq_one_of_isAlgClosed (r P₀)))
  haveI hfinK : FiniteDimensional K (riemannRochSpace (Finsupp.mapDomain r D)) :=
    AlgebraicCurve.finiteDimensional_lSpace (Finsupp.mapDomain r D)

  obtain ⟨O, ρ, hOA, hker, hconstσ, hreg, hρF⟩ :=
    AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring
      K F E FE hfg hfgE hgen A hKA (sigma A hKA hArat) (ker_sigma A hKA hArat)
      (sigma_algebraMap A hKA hArat)
  have hFO : ∀ f : F, algebraMap F FE f ∈ O := fun f => (hρF f).1
  have hρF' : ∀ (f : F) (h : algebraMap F FE f ∈ O), ρ ⟨algebraMap F FE f, h⟩ = f :=
    fun f h => by obtain ⟨h', e⟩ := hρF f; exact e
  have hsurj : Function.Surjective ρ := fun f => ⟨_, hρF' f (hFO f)⟩

  let ιK : K →+* A := (algebraMap K E).codRestrict A hKA
  let φ : K →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp ιK
  have hφσ : ∀ a : A, φ (sigma A hKA hArat a) = IsLocalRing.residue A a := fun a => by
    show IsLocalRing.residue A (ιK _) = _
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← ker_sigma A hKA hArat,
      RingHom.mem_ker, map_sub, sub_eq_zero]
    exact sigma_algebraMap A hKA hArat _
  have hφ : Function.Bijective φ :=
    ⟨φ.injective, fun z => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
      exact ⟨_, hφσ a⟩⟩
  let e : K ≃+* IsLocalRing.ResidueField A := RingEquiv.ofBijective φ hφ
  letI iK : Algebra (IsLocalRing.ResidueField A) K := e.symm.toRingHom.toAlgebra
  letI iF : Algebra (IsLocalRing.ResidueField A) F :=
    ((algebraMap K F).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower (IsLocalRing.ResidueField A) K F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkK : Function.Surjective (algebraMap (IsLocalRing.ResidueField A) K) := e.symm.surjective
  have hkKb : Function.Bijective (algebraMap (IsLocalRing.ResidueField A) K) := e.symm.bijective
  have he_symm : ∀ a : A, e.symm (IsLocalRing.residue A a) = sigma A hKA hArat a := fun a => by
    rw [RingEquiv.symm_apply_eq]
    exact (hφσ a).symm
  have hconst : ∀ a : A, ρ ⟨algebraMap E FE a, (hOA a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) F (IsLocalRing.residue A a) := fun a => by
    obtain ⟨h, hh⟩ := hconstσ a
    rw [hh]
    show algebraMap K F _ = algebraMap K F (e.symm _)
    rw [he_symm]
  let R : RegularProlongation A FE F :=
    { integers := O, residue := ρ, algebraMap_mem_iff := hOA, residue_surjective := hsurj,
      ker_residue := hker, residue_algebraMap := hconst, exists_smul_mem := hreg }

  obtain ⟨hx₀k, hfink, hfinrk⟩ := transfer_fg hkK hx₀ hfin₀
  have hCa := AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank A R
    ⟨algebraMap F FE x₀, hFO x₀⟩
    (by rw [show R.residue ⟨algebraMap F FE x₀, hFO x₀⟩ = x₀ from hρF' x₀ _]; exact hx₀k)
    (by
      rw [show R.residue ⟨algebraMap F FE x₀, hFO x₀⟩ = x₀ from hρF' x₀ _]
      haveI := hfink; exact Module.finrank_pos)
    (by
      rw [show R.residue ⟨algebraMap F FE x₀, hFO x₀⟩ = x₀ from hρF' x₀ _]
      show Module.finrank (IntermediateField.adjoin E ({algebraMap F FE x₀} : Set FE)) FE = _
      rw [finrank_adjoin_algebraMap_eq hfg hfgE hgen hx₀ hfin₀, hfinrk])
    (riemannRochSpace D)

  set S : Set F :=
    {h : F | ∃ f : R.integers, (f : FE) ∈ riemannRochSpace D ∧ R.residue f = h} with hS_def
  have hS : S ⊆ (riemannRochSpace (Finsupp.mapDomain r D) : Set F) := by
    rintro _ ⟨f, hfD, rfl⟩
    by_cases hf0 : R.residue f = 0
    · rw [hf0]; exact Submodule.zero_mem _
    have hfne : (f : FE) ≠ 0 := fun h => hf0 (by
      have : f = 0 := Subtype.ext h
      rw [this, map_zero])
    obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := E) (f : FE) hfne
    have hcomp : ∀ v, Finsupp.mapDomain r Df v = v.ord (ρ f) := fun v =>
      AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction K F E FE hfg hfgE hgen
        A r hKA hArat hr O ρ hOA hker hρF f hf0 Df hDf v
    refine mem_riemannRochSpace_iff.mpr fun v => Or.inr ?_
    have hnn : ∀ P, 0 ≤ (Df + D) P := fun P => by
      rw [Finsupp.add_apply, hDf]
      have := ((mem_riemannRochSpace_iff.mp hfD) P).resolve_left hfne
      linarith
    have h := mapDomain_nonneg r hnn v
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, hcomp] at h
    change -(Finsupp.mapDomain r D v) ≤ v.ord (ρ f)
    linarith

  have hspan : Submodule.span (IsLocalRing.ResidueField A) S ≤
      (riemannRochSpace (Finsupp.mapDomain r D)).restrictScalars (IsLocalRing.ResidueField A) :=
    Submodule.span_le.mpr hS
  haveI : Module.Finite (IsLocalRing.ResidueField A) K :=
    Module.Finite.of_surjective (Algebra.linearMap (IsLocalRing.ResidueField A) K) hkK
  have hfk : Module.Finite (IsLocalRing.ResidueField A)
      (riemannRochSpace (Finsupp.mapDomain r D)) :=
    Module.Finite.trans K _
  haveI : Module.Finite (IsLocalRing.ResidueField A)
      ((riemannRochSpace (Finsupp.mapDomain r D)).restrictScalars
        (IsLocalRing.ResidueField A)) := hfk
  calc Module.finrank E (riemannRochSpace D)
      = Module.finrank (IsLocalRing.ResidueField A)
          (Submodule.span (IsLocalRing.ResidueField A) S) := hCa.symm
    _ ≤ Module.finrank (IsLocalRing.ResidueField A)
          ((riemannRochSpace (Finsupp.mapDomain r D)).restrictScalars
            (IsLocalRing.ResidueField A)) := Submodule.finrank_mono hspan
    _ = Module.finrank (IsLocalRing.ResidueField A)
          (riemannRochSpace (Finsupp.mapDomain r D)) := rfl
    _ = Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) :=
        finrank_eq_of_bijective_algebraMap hkKb

end DeuringLowerSemicontinuity

theorem solution
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE)
    (A : ValuationSubring E) (r : Place E FE → Place K F)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) :
    Module.finrank E (riemannRochSpace D) ≤
      Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) :=
  DeuringLowerSemicontinuity.main K F E FE hfg hfgE hgen D A r hKA hArat hr

end S_AlgebraicCurve_Divisor_finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction (solution)
