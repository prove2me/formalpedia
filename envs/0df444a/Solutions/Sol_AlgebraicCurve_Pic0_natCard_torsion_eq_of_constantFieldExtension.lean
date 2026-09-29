-- Prove2me | solution 1 for AlgebraicCurve.Pic0.natCard_torsion_eq_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/077075dc-044a-59b3-9fe3-3da9080fb265

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

open scoped IntermediateField.algebraAdjoinAdjoin
open Module

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.ord_inv Place.ord_zpow Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective Pic0.torsion Pic0.mem_torsion HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed linearIndependent_of_constantFieldExtension Place.exists_comap_algebraMap_eq_of_constantFieldExtension Place.exists_toValuationSubring_eq_comap_ringHom Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed Divisor.exists_torsion_descent_of_constantFieldExtension"
namespace W7XL2
p2m_open "AlgebraicCurve"

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

theorem finiteDimensional_adjoin_simple_algebraMap {K A B : Type*} [Field K] [Field A] [Field B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [FiniteDimensional A B]
    (x : A) [hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set A)) A] :
    FiniteDimensional (IntermediateField.adjoin K ({algebraMap A B x} : Set B)) B := by
  set E := IntermediateField.adjoin K ({x} : Set A) with hE
  set E' := IntermediateField.adjoin K ({algebraMap A B x} : Set B) with hE'
  have hmap : ∀ e : E, algebraMap A B (e : A) ∈ E' := fun e =>
    algebraMap_mem_adjoin_simple (K' := K) x e.2
  let φ : E →+* E' := ((algebraMap A B).comp (algebraMap E A)).codRestrict E' hmap
  letI : Algebra E E' := φ.toAlgebra
  haveI : IsScalarTower E E' B := IsScalarTower.of_algebraMap_eq (fun e => rfl)
  haveI : Module.Finite E B := Module.Finite.trans A B
  exact Module.Finite.of_restrictScalars_finite E E' B

section KL

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem mem_range_of_pow_eq_algebraMap [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {n : ℕ} (hn : n ≠ 0) {y : F'} {g : F} (hy : y ^ n = algebraMap F F' g) :
    y ∈ (algebraMap F F').range := by
  classical
  obtain ⟨x, hx, hfin⟩ := hfg
  haveI := hfin
  set E : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hE
  have hyint : IsIntegral F y :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by rw [hy]; exact isIntegral_algebraMap)
  set S : IntermediateField F F' := IntermediateField.adjoin F ({y} : Set F') with hS
  haveI : FiniteDimensional F S := IntermediateField.adjoin.finiteDimensional hyint
  set x' : F' := algebraMap F F' x with hx'
  set E' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hE'
  set m := finrank E F with hm_def
  set d := finrank F S with hd_def
  let bF := Module.finBasis E F
  let bS := Module.finBasis F S
  have hm : 0 < m := Module.finrank_pos
  haveI i2 : IsScalarTower K S F' := IsScalarTower.of_algebraMap_eq (fun k => rfl)

  let xE : E := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hxEt : Transcendental K xE := by
    have : Function.Injective (algebraMap E F) := (algebraMap E F).injective
    rw [← transcendental_algebraMap_iff this]
    exact hx
  have hpow : LinearIndependent K fun k : ℕ => xE ^ k := linearIndependent_pow_of_transcendental hxEt
  have h1 : LinearIndependent K fun q : ℕ × Fin m => (xE ^ q.1 • bF q.2 : F) :=
    linearIndependent_smul hpow bF.linearIndependent
  have h2 : LinearIndependent F fun j : Fin d => ((bS j : S) : F') :=
    bS.linearIndependent.map' S.val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hfam' : LinearIndependent K fun q : (ℕ × Fin m) × Fin d =>
      (xE ^ q.1.1 • bF q.1.2 : F) • ((bS q.2 : S) : F') := by
    exact linearIndependent_smul (R := K) (S := F) (A := F') (ι := ℕ × Fin m) (ι' := Fin d)
      (b := fun q : ℕ × Fin m => (xE ^ q.1 • bF q.2 : F)) (c := fun j => ((bS j : S) : F')) h1 h2
  have hmem : ∀ q : (ℕ × Fin m) × Fin d,
      (xE ^ q.1.1 • bF q.1.2 : F) • ((bS q.2 : S) : F') ∈ S := fun q => by
    rw [Algebra.smul_def]
    exact S.mul_mem (S.algebraMap_mem _) (bS q.2).2
  let v : (ℕ × Fin m) × Fin d → S := fun q => ⟨_, hmem q⟩
  have hfam : LinearIndependent K v :=
    LinearIndependent.of_comp (IsScalarTower.toAlgHom K S F').toLinearMap hfam'

  have hfgS : ∃ z : S, Transcendental K z ∧
      FiniteDimensional (IntermediateField.adjoin K ({z} : Set S)) S :=
    ⟨algebraMap F S x, (transcendental_algebraMap_iff (algebraMap F S).injective).mpr hx,
      finiteDimensional_adjoin_simple_algebraMap x⟩
  have hgenS : IntermediateField.adjoin K' (Set.range (algebraMap S F')) = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨f, rfl⟩
    exact IntermediateField.subset_adjoin K' _
      ⟨algebraMap F S f, (IsScalarTower.algebraMap_apply F S F' f).symm⟩
  have hW := AlgebraicCurve.linearIndependent_of_constantFieldExtension K S K' F' hfgS hfg' hgenS
    hfam
  have hW' : LinearIndependent K' fun p : ℕ × (Fin m × Fin d) =>
      x' ^ p.1 * (algebraMap F F' (bF p.2.1) * (bS p.2.2 : F')) := by
    have := hW.comp _ (Equiv.prodAssoc ℕ (Fin m) (Fin d)).symm.injective
    convert this using 1
    funext p
    simp only [Function.comp_apply, Equiv.prodAssoc_symm_apply, hx',
      IntermediateField.algebraMap_apply, Algebra.smul_def, map_mul, map_pow, v]
    ring

  set u : Fin m × Fin d → F' := fun p => algebraMap F F' (bF p.1) * (bS p.2 : F') with hu_def
  have hu : LinearIndependent E' u := linearIndependent_adjoin_simple_of_pow_mul x' u hW'

  set b' : Fin m → F' := fun i => algebraMap F F' (bF i) with hb'
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

  have hcard := hu.fintype_card_le_finrank
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  have hd1 : d = 1 := by
    have h3 : 0 < d := Module.finrank_pos
    have h1 : m * d ≤ m * 1 := by rw [mul_one]; exact hcard.trans hle
    have h2 : d ≤ 1 := Nat.le_of_mul_le_mul_left h1 hm
    omega
  have hyb : y ∈ (⊥ : IntermediateField F F') :=
    IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hd1
  rw [IntermediateField.mem_bot] at hyb
  obtain ⟨f, hf⟩ := hyb
  exact ⟨f, hf⟩

end KL

section Transfer

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem ord_eq_zero_of_mem_of_inv_mem {k L : Type*} [Field k] [Field L] [Algebra k L]
    (w : Place k L) {z : L} (hz : z ∈ w.toValuationSubring)
    (hzi : z⁻¹ ∈ w.toValuationSubring) : w.ord z = 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · exact w.ord_zero
  · let u : w.toValuationSubringˣ :=
      ⟨⟨z, hz⟩, ⟨z⁻¹, hzi⟩, Subtype.ext (mul_inv_cancel₀ hz0), Subtype.ext (inv_mul_cancel₀ hz0)⟩
    exact w.ord_coe_unit u

theorem ord_algebraMap_base {k L : Type*} [Field k] [Field L] [Algebra k L]
    (w : Place k L) (a : k) : w.ord (algebraMap k L a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero]; exact w.ord_zero
  · refine ord_eq_zero_of_mem_of_inv_mem w (w.algebraMap_mem' a) ?_
    rw [← map_inv₀]
    exact w.algebraMap_mem' _

theorem degree_eq_zero_of_forall_eq_ord {k L : Type*} [Field k] [Field L] [Algebra k L]
    [HasPrincipalDivisors k L] {f : L} (hf : f ≠ 0) {D : Divisor k L}
    (hD : ∀ v, D v = v.ord f) : Divisor.degree D = 0 := by
  obtain ⟨E, hE, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) f hf
  have : D = E := Finsupp.ext fun v => by rw [hD, hE]
  rw [this]
  exact hdeg

theorem mk_zsmul' {k L : Type*} [Field k] [Field L] [Algebra k L] (n : ℤ)
    (D : Divisor.degZero (K := k) (F := L)) : Pic0.mk (n • D) = n • Pic0.mk D :=
  QuotientAddGroup.mk_zsmul _ D n

theorem mk_eq_zero_iff' {k L : Type*} [Field k] [Field L] [Algebra k L]
    (D : Divisor.degZero (K := k) (F := L)) :
    Pic0.mk D = 0 ↔ (D : Divisor k L) ∈ (Divisor.principal : AddSubgroup (Divisor k L)) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

theorem mk_eq_mk_iff' {k L : Type*} [Field k] [Field L] [Algebra k L]
    (D E : Divisor.degZero (K := k) (F := L)) :
    Pic0.mk D = Pic0.mk E ↔
      -(D : Divisor k L) + E ∈ (Divisor.principal : AddSubgroup (Divisor k L)) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  exact Iff.rfl

theorem natCast_mul_apply_eq_of_zsmul_mem_principal {k L : Type*} [Field k] [Field L]
    [Algebra k L] {n : ℕ} {D : Divisor.degZero (K := k) (F := L)}
    (h : ((n : ℤ) • D : Divisor.degZero (K := k) (F := L)) ∈
      (Divisor.principal : AddSubgroup (Divisor k L)).addSubgroupOf Divisor.degZero) :
    ∃ g : L, g ≠ 0 ∧ ∀ v : Place k L, (n : ℤ) * (D : Divisor k L) v = v.ord g := by
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨g, hg, hDg⟩ := h
  refine ⟨g, hg, fun v => ?_⟩
  rw [← hDg v, AddSubgroupClass.coe_zsmul, Finsupp.smul_apply, smul_eq_mul]

section Lift

variable [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
  (hfg : ∃ x : F, Transcendental K x ∧
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
  (hfg' : ∃ x : F', Transcendental K' x ∧
    FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
  (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)

noncomputable def liftPlace (P : Place K F) : Place K' F' :=
  Classical.choose
    (AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen P)

theorem liftPlace_spec (P : Place K F) :
    (liftPlace hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') =
        P.toValuationSubring ∧
      (∀ f : F, (liftPlace hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : Place K' F', Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
        Q' = liftPlace hfg hfg' hgen P :=
  Classical.choose_spec
    (AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen P)

theorem liftPlace_comap (P : Place K F) :
    (liftPlace hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') =
      P.toValuationSubring :=
  (liftPlace_spec hfg hfg' hgen P).1

theorem ord_liftPlace (P : Place K F) (f : F) :
    (liftPlace hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f :=
  (liftPlace_spec hfg hfg' hgen P).2.1 f

theorem eq_liftPlace {P : Place K F} {Q' : Place K' F'}
    (h : Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) :
    Q' = liftPlace hfg hfg' hgen P :=
  (liftPlace_spec hfg hfg' hgen P).2.2 Q' h

theorem liftPlace_injective :
    Function.Injective (liftPlace (K := K) (F := F) (K' := K') (F' := F') hfg hfg' hgen) := by
  intro P Q h
  apply Place.ext
  rw [← liftPlace_comap hfg hfg' hgen P, h, liftPlace_comap]

theorem ord_algebraMap_eq_zero_of_forall_ne (w : Place K' F')
    (hw : ∀ P : Place K F, w ≠ liftPlace hfg hfg' hgen P) (f : F) :
    w.ord (algebraMap F F' f) = 0 := by
  by_contra hne
  obtain ⟨x, hx, hfin⟩ := id hfg
  haveI := hfin
  have hwK : ∀ a : K, algebraMap F F' (algebraMap K F a) ∈ w.toValuationSubring := fun a => by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K K' F']
    exact w.algebraMap_mem' _
  have hwx : ∃ y : F, algebraMap F F' y ∉ w.toValuationSubring := by
    by_contra hall
    push Not at hall
    exact hne (ord_eq_zero_of_mem_of_inv_mem w (hall f) (by rw [← map_inv₀]; exact hall _))
  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom
    (K := K) x (algebraMap F F') w.toValuationSubring hwK hwx
  exact hw v (eq_liftPlace hfg hfg' hgen hv.symm)

noncomputable def conormDiv : Divisor K F →+ Divisor K' F' :=
  Finsupp.mapDomain.addMonoidHom (liftPlace hfg hfg' hgen)

theorem conormDiv_apply_liftPlace (D : Divisor K F) (P : Place K F) :
    conormDiv hfg hfg' hgen D (liftPlace hfg hfg' hgen P) = D P :=
  Finsupp.mapDomain_apply (liftPlace_injective hfg hfg' hgen) D P

theorem conormDiv_apply_of_forall_ne (D : Divisor K F) (w : Place K' F')
    (hw : ∀ P : Place K F, w ≠ liftPlace hfg hfg' hgen P) : conormDiv hfg hfg' hgen D w = 0 :=
  Finsupp.mapDomain_notin_range D w (by rintro ⟨P, rfl⟩; exact hw P rfl)

theorem conormDiv_single (P : Place K F) (m : ℤ) :
    conormDiv hfg hfg' hgen (Finsupp.single P m) = Finsupp.single (liftPlace hfg hfg' hgen P) m :=
  Finsupp.mapDomain_single

theorem conormDiv_mem_principal {D : Divisor K F}
    (hD : D ∈ (Divisor.principal : AddSubgroup (Divisor K F))) :
    conormDiv hfg hfg' hgen D ∈ (Divisor.principal : AddSubgroup (Divisor K' F')) := by
  obtain ⟨f, hf, hDf⟩ := hD
  refine ⟨algebraMap F F' f, (map_ne_zero _).mpr hf, fun w => ?_⟩
  by_cases hw : ∃ P, w = liftPlace hfg hfg' hgen P
  · obtain ⟨P, rfl⟩ := hw
    rw [conormDiv_apply_liftPlace, ord_liftPlace, hDf]
  · push Not at hw
    rw [conormDiv_apply_of_forall_ne hfg hfg' hgen D w hw,
      ord_algebraMap_eq_zero_of_forall_ne hfg hfg' hgen w hw]

variable [IsAlgClosed K'] [IsCurveOver K' F']

theorem degree_conormDiv (D : Divisor K F) :
    Divisor.degree (conormDiv hfg hfg' hgen D) = Divisor.degree D := by
  refine Finsupp.induction D (by simp) fun P m D _ _ ih => ?_
  rw [map_add, map_add, map_add, ih, conormDiv_single, Divisor.degree_single,
    Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed,
    IsCurveOver.deg_eq_one_of_isAlgClosed]

noncomputable def conormDegZero :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K') (F := F') :=
  ((conormDiv hfg hfg' hgen).domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => show Divisor.degree (conormDiv hfg hfg' hgen (D : Divisor K F)) = 0 by
      rw [degree_conormDiv]; exact D.2)

theorem coe_conormDegZero (D : Divisor.degZero (K := K) (F := F)) :
    (conormDegZero hfg hfg' hgen D : Divisor K' F') = conormDiv hfg hfg' hgen D := rfl

noncomputable def Con : Pic0 K F →+ Pic0 K' F' :=
  QuotientAddGroup.map _ _ (conormDegZero hfg hfg' hgen) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact conormDiv_mem_principal hfg hfg' hgen hD)

theorem Con_mk (D : Divisor.degZero (K := K) (F := F)) :
    Con hfg hfg' hgen (Pic0.mk D) = Pic0.mk (conormDegZero hfg hfg' hgen D) := rfl

theorem Con_eq_zero_imp {n : ℕ} (hn : n ≠ 0) {c : Pic0 K F}
    (hc : c ∈ Pic0.torsion K F n) (h0 : Con hfg hfg' hgen c = 0) : c = 0 := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [Con_mk, mk_eq_zero_iff', coe_conormDegZero] at h0
  obtain ⟨f', hf', hDf'⟩ := h0
  rw [Pic0.mem_torsion, ← mk_zsmul', mk_eq_zero_iff', ← AddSubgroup.mem_addSubgroupOf] at hc
  obtain ⟨g, hg, hDg⟩ := natCast_mul_apply_eq_of_zsmul_mem_principal hc
  have hg' : algebraMap F F' g ≠ 0 := (map_ne_zero _).mpr hg

  set z : F' := f' ^ n * (algebraMap F F' g)⁻¹ with hz
  have hz0 : z ≠ 0 := mul_ne_zero (pow_ne_zero _ hf') (inv_ne_zero hg')
  have hzord : ∀ w : Place K' F', w.ord z = 0 := by
    intro w
    rw [hz, w.ord_mul (pow_ne_zero _ hf') (inv_ne_zero hg'), Place.ord_inv, ← zpow_natCast,
      Place.ord_zpow]
    by_cases hw : ∃ P, w = liftPlace hfg hfg' hgen P
    · obtain ⟨P, rfl⟩ := hw
      rw [ord_liftPlace, ← hDg P, ← hDf', conormDiv_apply_liftPlace]
      ring
    · push Not at hw
      rw [← hDf', conormDiv_apply_of_forall_ne hfg hfg' hgen _ w hw,
        ord_algebraMap_eq_zero_of_forall_ne hfg hfg' hgen w hw]
      ring
  obtain ⟨x', hx', hfin'⟩ := id hfg'
  haveI := hfin'
  obtain ⟨c, hc⟩ :=
    AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
      (K := K') x' hx' hzord
  have hc0 : c ≠ 0 := by rintro rfl; exact hz0 (by rw [← hc, map_zero])

  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hn)
  have hd0 : d ≠ 0 := by rintro rfl; exact hc0 (by rw [← hd, zero_pow hn])
  have hd0' : algebraMap K' F' d ≠ 0 := (map_ne_zero _).mpr hd0

  set y : F' := f' * (algebraMap K' F' d)⁻¹ with hy_def
  have hy : y ^ n = algebraMap F F' g := by
    rw [hy_def, mul_pow, inv_pow, ← map_pow, hd, hc, hz, mul_inv, inv_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hf'), one_mul]
  obtain ⟨f, hf⟩ := mem_range_of_pow_eq_algebraMap hfg hfg' hgen hn hy
  have hfy : f' = algebraMap F F' f * algebraMap K' F' d := by
    rw [hf, hy_def, inv_mul_cancel_right₀ hd0']
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hfy
    exact hf' hfy

  refine (mk_eq_zero_iff' D).mpr ⟨f, hf0, fun P => ?_⟩
  rw [← ord_liftPlace hfg hfg' hgen P f, ← conormDiv_apply_liftPlace hfg hfg' hgen (D : Divisor K F) P,
    hDf', hfy, (liftPlace hfg hfg' hgen P).ord_mul ((map_ne_zero _).mpr hf0) hd0',
    ord_algebraMap_base, add_zero]

theorem exists_Con_eq {n : ℕ} (hn : n ≠ 0) {c' : Pic0 K' F'}
    (hc' : c' ∈ Pic0.torsion K' F' n) :
    ∃ c ∈ Pic0.torsion K F n, Con hfg hfg' hgen c = c' := by
  obtain ⟨D', rfl⟩ := Pic0.mk_surjective c'
  have hc'' := hc'
  rw [Pic0.mem_torsion, ← mk_zsmul', mk_eq_zero_iff', ← AddSubgroup.mem_addSubgroupOf] at hc''
  obtain ⟨g', hg', hDg'⟩ := natCast_mul_apply_eq_of_zsmul_mem_principal hc''
  obtain ⟨D, h', hh', ⟨g, hg, hDg⟩, hover, hoff⟩ :=
    AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension K F K' F' hfg hfg'
      hgen n hn (D' : Divisor K' F') ⟨g', hg', hDg'⟩
  have hDdeg : Divisor.degree D = 0 := by
    have h1 : Divisor.degree ((n : ℤ) • D) = 0 :=
      degree_eq_zero_of_forall_eq_ord hg fun v => by rw [Finsupp.smul_apply, smul_eq_mul, hDg]
    rw [map_zsmul, smul_eq_mul, mul_eq_zero] at h1
    exact h1.resolve_left (Int.natCast_ne_zero.mpr hn)
  refine ⟨Pic0.mk ⟨D, Divisor.mem_degZero.mpr hDdeg⟩, ?_, ?_⟩
  · rw [Pic0.mem_torsion, ← mk_zsmul', mk_eq_zero_iff']
    exact ⟨g, hg, fun v => by
      rw [AddSubgroupClass.coe_zsmul, Finsupp.smul_apply, smul_eq_mul]; exact hDg v⟩
  · rw [Con_mk, mk_eq_mk_iff', coe_conormDegZero]
    refine ⟨h', hh', fun w => ?_⟩
    rw [Finsupp.add_apply, Finsupp.neg_apply]
    by_cases hw : ∃ P, w = liftPlace hfg hfg' hgen P
    · obtain ⟨P, rfl⟩ := hw
      rw [conormDiv_apply_liftPlace, hover P _ (liftPlace_comap hfg hfg' hgen P)]
      ring
    · push Not at hw
      have hoffw := hoff w fun P hP => hw P (eq_liftPlace hfg hfg' hgen hP)
      rw [conormDiv_apply_of_forall_ne hfg hfg' hgen _ w hw, hoffw]
      ring

include hfg hfg' hgen in

theorem natCard_torsion_eq {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Pic0.torsion K' F' n) = Nat.card (Pic0.torsion K F n) := by
  let t : Pic0.torsion K F n → Pic0.torsion K' F' n := fun c =>
    ⟨Con hfg hfg' hgen c, by
      rw [Pic0.mem_torsion, ← map_zsmul (Con hfg hfg' hgen), Pic0.mem_torsion.mp c.2, map_zero]⟩
  have hinj : Function.Injective t := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    have h' : Con hfg hfg' hgen a = Con hfg hfg' hgen b := congrArg Subtype.val h
    have hab : a - b ∈ Pic0.torsion K F n := (Pic0.torsion K F n).sub_mem ha hb
    have := Con_eq_zero_imp hfg hfg' hgen hn hab (by rw [map_sub, h', sub_self])
    exact Subtype.ext (sub_eq_zero.mp this)
  have hsurj : Function.Surjective t := by
    rintro ⟨c', hc'⟩
    obtain ⟨c, hc, hcc'⟩ := exists_Con_eq hfg hfg' hgen hn hc'
    exact ⟨⟨c, hc⟩, Subtype.ext hcc'⟩
  exact (Nat.card_congr (Equiv.ofBijective t ⟨hinj, hsurj⟩)).symm

end Lift

end Transfer

end AlgebraicCurve.W7XL2

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension.AlgebraicCurve"

theorem solution (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Pic0.torsion K' F' n) = Nat.card (Pic0.torsion K F n) :=
  AlgebraicCurve.W7XL2.natCard_torsion_eq hfg hfg' hgen hn

end S_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension (solution)
