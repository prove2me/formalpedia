-- Prove2me | solution 1 for AlgebraicCurve.exists_divisor_degree_eq_one_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/39a0ad51-7c6b-50ca-9997-34e9de1980c7

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum
import Theorems.Thm_AlgebraicCurve_exists_constantFieldExtension_of_finite
import Theorems.Thm_AlgebraicCurve_card_places_deg_one_eq_sum_divisors_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Pic0_finite_of_finite
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_divisor_degree_eq_one_of_finite
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finiteResidue Place Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective HasPrincipalDivisors.exists_divisor LSpace ell mem_lSpace_iff_ord ConstantsAreBase ell_zero_eq_one_of_constantsAreBase genusFF card_effectiveDivisors_mul_eq_sum exists_constantFieldExtension_of_finite card_places_deg_one_eq_sum_divisors_of_constantFieldExtension Pic0.finite_of_finite stichtenothGenusExists_of_isCurveOver Place.ord_eq_zero_of_isAlgebraic indexOfSpecialty_eq_of_genusReached indexOfSpecialty_eq_finrank_H1 finiteDimensional_lSpace"
namespace ClassCountFinite
p2m_open "AlgebraicCurve"

open scoped LinearAlgebra.Projectivization

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

section Principal

variable [HasPrincipalDivisors K E]

variable (K) in

noncomputable def pdiv (f : E) : Divisor K E :=
  haveI := Classical.dec (f = 0)
  if hf : f = 0 then 0 else (HasPrincipalDivisors.exists_divisor (K := K) f hf).choose

theorem pdiv_apply (f : E) (v : Place K E) : pdiv K f v = v.ord f := by
  unfold pdiv
  split_ifs with hf
  · simp [hf]
  · exact (HasPrincipalDivisors.exists_divisor (K := K) f hf).choose_spec.1 v

theorem degree_pdiv (f : E) : Divisor.degree (pdiv K f) = 0 := by
  unfold pdiv
  split_ifs with hf
  · simp
  · exact (HasPrincipalDivisors.exists_divisor (K := K) f hf).choose_spec.2

theorem pdiv_mul {f g : E} (hf : f ≠ 0) (hg : g ≠ 0) :
    pdiv K (f * g) = pdiv K f + pdiv K g := by
  ext v
  simp only [Finsupp.add_apply, pdiv_apply, v.ord_mul hf hg]

theorem pdiv_inv (f : E) : pdiv K f⁻¹ = -pdiv K f := by
  ext v
  simp only [Finsupp.neg_apply, pdiv_apply, v.ord_inv]

theorem pdiv_mem_principal {f : E} (hf : f ≠ 0) :
    pdiv K f ∈ Divisor.principal (K := K) (F := E) :=
  ⟨f, hf, pdiv_apply f⟩

theorem eq_pdiv_of_forall {D : Divisor K E} {f : E} (h : ∀ v : Place K E, D v = v.ord f) :
    D = pdiv K f := by
  ext v
  rw [h v, pdiv_apply]

theorem degree_eq_zero_of_mem_principal {D : Divisor K E}
    (hD : D ∈ Divisor.principal (K := K) (F := E)) : Divisor.degree D = 0 := by
  obtain ⟨f, -, h⟩ := hD
  rw [eq_pdiv_of_forall h, degree_pdiv]

theorem mem_lSpace_iff_pdiv {D : Divisor K E} {f : E} (hf : f ≠ 0) :
    f ∈ LSpace D ↔ 0 ≤ D + pdiv K f := by
  rw [mem_lSpace_iff_ord, or_iff_right hf, Finsupp.le_def]
  refine forall_congr' fun v => ?_
  rw [Finsupp.add_apply, pdiv_apply, Finsupp.coe_zero, Pi.zero_apply]
  constructor <;> intro h <;> linarith

theorem pdiv_algebraMap (c : K) : pdiv K (algebraMap K E c) = 0 := by
  ext v
  rw [pdiv_apply, Finsupp.coe_zero, Pi.zero_apply]
  exact v.ord_eq_zero_of_isAlgebraic (isAlgebraic_algebraMap c)

theorem exists_eq_algebraMap_of_pdiv_eq_zero (hC : ConstantsAreBase K E) {f : E} (hf : f ≠ 0)
    (h : pdiv K f = 0) : ∃ c : K, c ≠ 0 ∧ algebraMap K E c = f := by
  have hmem : f ∈ LSpace (0 : Divisor K E) := by
    rw [mem_lSpace_iff_pdiv hf, h, add_zero]
  rw [hC] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_, hc⟩
  rintro rfl
  exact hf (by simpa using hc.symm)

end Principal

section InClass

variable [IsCurveOver K E]

abbrev EffCl (C : Divisor K E) : Type _ :=
  {D : Divisor K E // 0 ≤ D ∧ D - C ∈ Divisor.principal (K := K) (F := E)}

omit [IsCurveOver K E] in
theorem coe_ne_zero_of {C : Divisor K E} (f : {w : LSpace C // w ≠ 0}) : ((f.1 : LSpace C) : E) ≠ 0 :=
  fun h => f.2 (ZeroMemClass.coe_eq_zero.mp h)

noncomputable def effOf (C : Divisor K E) (f : {w : LSpace C // w ≠ 0}) : EffCl C :=
  ⟨C + pdiv K (f.1 : E), (mem_lSpace_iff_pdiv (coe_ne_zero_of f)).mp f.1.2, by
    rw [add_sub_cancel_left]; exact pdiv_mem_principal (coe_ne_zero_of f)⟩

theorem effOf_smul (C : Divisor K E) (a b : {w : LSpace C // w ≠ 0}) (t : K)
    (h : (a : LSpace C) = t • (b : LSpace C)) : effOf C a = effOf C b := by
  have ht : t ≠ 0 := by
    rintro rfl
    exact a.2 (by rw [h, zero_smul])
  apply Subtype.ext
  change C + pdiv K ((a.1 : LSpace C) : E) = C + pdiv K ((b.1 : LSpace C) : E)
  rw [h, Submodule.coe_smul, Algebra.smul_def,
    pdiv_mul ((map_ne_zero (algebraMap K E)).mpr ht) (coe_ne_zero_of b), pdiv_algebraMap,
    zero_add]

noncomputable def effOfP (C : Divisor K E) : ℙ K (LSpace C) → EffCl C :=
  Projectivization.lift (effOf C) (effOf_smul C)

theorem effOfP_bijective (hC : ConstantsAreBase K E) (C : Divisor K E) :
    Function.Bijective (effOfP (K := K) C) := by
  constructor
  · intro p q
    induction p using Projectivization.ind with
    | h a ha =>
    induction q using Projectivization.ind with
    | h b hb =>
    intro hab
    rw [effOfP, Projectivization.lift_mk, Projectivization.lift_mk] at hab
    have hab' : pdiv K (a : E) = pdiv K (b : E) := by
      have := congrArg Subtype.val hab
      exact add_left_cancel this
    have ha0 : (a : E) ≠ 0 := coe_ne_zero_of ⟨a, ha⟩
    have hb0 : (b : E) ≠ 0 := coe_ne_zero_of ⟨b, hb⟩
    have hq : pdiv K ((a : E) * (b : E)⁻¹) = 0 := by
      rw [pdiv_mul ha0 (inv_ne_zero hb0), pdiv_inv, hab', add_neg_cancel]
    obtain ⟨c, hc, hce⟩ :=
      exists_eq_algebraMap_of_pdiv_eq_zero hC (mul_ne_zero ha0 (inv_ne_zero hb0)) hq
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 c hc, ?_⟩
    rw [Units.smul_mk0]
    apply Subtype.ext
    rw [Submodule.coe_smul, Algebra.smul_def, hce, inv_mul_cancel_right₀ hb0]
  · rintro ⟨D, hD0, f, hf, hfD⟩
    have hDC : D - C = pdiv K f := eq_pdiv_of_forall hfD
    have hD : D = C + pdiv K f := by rw [← hDC, add_sub_cancel]
    have hfL : f ∈ LSpace C := by
      rw [mem_lSpace_iff_pdiv hf, ← hD]
      exact hD0
    have hne : (⟨f, hfL⟩ : LSpace C) ≠ 0 := fun h => hf (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K ⟨f, hfL⟩ hne, ?_⟩
    rw [effOfP, Projectivization.lift_mk]
    exact Subtype.ext hD.symm

theorem card_effCl_mul [Finite K] (hC : ConstantsAreBase K E) (C : Divisor K E)
    [FiniteDimensional K (LSpace C)] :
    Nat.card (EffCl (K := K) C) * (Nat.card K - 1) = Nat.card K ^ ell C - 1 := by
  rw [← Nat.card_eq_of_bijective _ (effOfP_bijective hC C), ← Projectivization.card,
    Module.natCard_eq_pow_finrank (K := K) (V := LSpace C)]

theorem finite_effCl [Finite K] (hC : ConstantsAreBase K E) (C : Divisor K E)
    [FiniteDimensional K (LSpace C)] : Finite (EffCl (K := K) C) := by
  haveI : Finite (LSpace C) := Module.finite_of_finite K
  exact Finite.of_surjective _ (effOfP_bijective hC C).2

theorem card_effCl_congr (C : Divisor K E) {f : E} (hf : f ≠ 0) :
    Nat.card (EffCl (K := K) C) = Nat.card (EffCl (K := K) (C + pdiv K f)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun D => and_congr_right fun _ => ?_)
  rw [show D - (C + pdiv K f) = (D - C) - pdiv K f by abel]
  exact ⟨fun h => sub_mem h (pdiv_mem_principal hf),
    fun h => by simpa using add_mem h (pdiv_mem_principal hf)⟩

end InClass

section Partition

variable [IsCurveOver K E]

theorem card_eff_degree_eq [Finite K] [Finite (Pic0 K E)] (n : ℕ) (D₁ : Divisor K E)
    (hD₁ : Divisor.degree D₁ = n) (M : ℕ)
    (hfin : ∀ C₀ : Divisor.degZero (K := K) (F := E),
      Finite (EffCl (K := K) (D₁ + (C₀ : Divisor K E))))
    (hcl : ∀ C₀ : Divisor.degZero (K := K) (F := E),
      Nat.card (EffCl (K := K) (D₁ + (C₀ : Divisor K E))) * (Nat.card K - 1) = M) :
    (Nat.card K - 1) * Nat.card {D : Divisor K E // 0 ≤ D ∧ Divisor.degree D = (n : ℤ)} =
      Nat.card (Pic0 K E) * M := by
  classical
  letI : Fintype (Pic0 K E) := Fintype.ofFinite _

  let π : {D : Divisor K E // 0 ≤ D ∧ Divisor.degree D = (n : ℤ)} → Pic0 K E := fun D =>
    Pic0.mk ⟨D.1 - D₁, by rw [Divisor.mem_degZero, map_sub, D.2.2, hD₁, sub_self]⟩

  have hfib : ∀ y : Pic0 K E, ∃ C₀ : Divisor.degZero (K := K) (F := E),
      Nonempty ({x // π x = y} ≃ EffCl (K := K) (D₁ + (C₀ : Divisor K E))) := by
    intro y
    obtain ⟨C₀, rfl⟩ := Pic0.mk_surjective y
    refine ⟨C₀, ⟨?_⟩⟩
    have key : ∀ (D : Divisor K E) (hD : 0 ≤ D ∧ Divisor.degree D = (n : ℤ)),
        π ⟨D, hD⟩ = Pic0.mk C₀ ↔
          D - (D₁ + (C₀ : Divisor K E)) ∈ Divisor.principal (K := K) (F := E) := by
      intro D hD
      simp only [π, Pic0.mk]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
        AddSubgroup.coe_neg]
      rw [show -(D - D₁) + (C₀ : Divisor K E) = -(D - (D₁ + C₀)) by abel, neg_mem_iff]
    exact
      { toFun := fun x => ⟨x.1.1, x.1.2.1, (key x.1.1 x.1.2).mp x.2⟩
        invFun := fun D => ⟨⟨D.1, D.2.1, by
            have h0 := degree_eq_zero_of_mem_principal D.2.2
            rw [map_sub, map_add, hD₁, C₀.2, add_zero, sub_eq_zero] at h0
            exact h0⟩, (key _ _).mpr D.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun D => rfl }
  haveI : ∀ y : Pic0 K E, Finite {x // π x = y} := fun y => by
    obtain ⟨C₀, ⟨e⟩⟩ := hfib y
    haveI := hfin C₀
    exact Finite.of_equiv _ e.symm
  have hcard : ∀ y : Pic0 K E, Nat.card {x // π x = y} * (Nat.card K - 1) = M := fun y => by
    obtain ⟨C₀, ⟨e⟩⟩ := hfib y
    rw [Nat.card_congr e, hcl C₀]
  calc (Nat.card K - 1) * Nat.card {D : Divisor K E // 0 ≤ D ∧ Divisor.degree D = (n : ℤ)}
      = (Nat.card K - 1) * Nat.card (Σ y : Pic0 K E, {x // π x = y}) := by
        rw [Nat.card_congr (Equiv.sigmaFiberEquiv π)]
    _ = ∑ y : Pic0 K E, Nat.card {x // π x = y} * (Nat.card K - 1) := by
        rw [Nat.card_sigma, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => mul_comm _ _
    _ = Nat.card (Pic0 K E) * M := by
        simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Fintype.card_eq_nat_card]

end Partition

section Riemann

variable [Finite K] [IsCurveOver K E] [Algebra.EssFiniteType K E]

theorem genus_data (hC : ConstantsAreBase K E) :
    ∃ D₀ : Divisor K E,
      (∀ D : Divisor K E, FiniteDimensional K (LSpace D)) ∧
      (∀ D : Divisor K E, Divisor.degree D + 1 - (genusFF K E : ℤ) ≤ ell D) ∧
      (∀ D : Divisor K E, D₀ ≤ D → (ell D : ℤ) = Divisor.degree D + 1 - (genusFF K E : ℤ)) := by
  obtain ⟨hne, hfin0, γ, D₀, hR⟩ := stichtenothGenusExists_of_isCurveOver hC
  haveI := hne
  haveI := hfin0
  have hγ : (genusFF K E : ℤ) = γ := by
    have h := (indexOfSpecialty_eq_of_genusReached hR (0 : Divisor K E)).2
    rw [indexOfSpecialty_eq_finrank_H1, ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h
    change (genusFF K E : ℤ) = _ at h
    rw [h]
    ring
  refine ⟨D₀, fun D => finiteDimensional_lSpace D, fun D => ?_, fun D hD => ?_⟩
  · have := hR.isMax D
    rw [hγ]
    linarith
  · have := hR.eq_of_ge hD
    rw [hγ]
    linarith

end Riemann

end AlgebraicCurve.ClassCountFinite

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finiteResidue Place Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective HasPrincipalDivisors.exists_divisor LSpace ell mem_lSpace_iff_ord ConstantsAreBase ell_zero_eq_one_of_constantsAreBase genusFF card_effectiveDivisors_mul_eq_sum exists_constantFieldExtension_of_finite card_places_deg_one_eq_sum_divisors_of_constantFieldExtension Pic0.finite_of_finite stichtenothGenusExists_of_isCurveOver Place.ord_eq_zero_of_isAlgebraic indexOfSpecialty_eq_of_genusReached indexOfSpecialty_eq_finrank_H1 finiteDimensional_lSpace" namespace ClassCountFinite end AlgebraicCurve.ClassCountFinite
p2m_open_scoped "AlgebraicCurve" in
open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_divisor_degree_eq_one_of_finite.AlgebraicCurve AlgebraicCurve.ClassCountFinite in

theorem AlgebraicCurve.ClassCountFinite.classCount
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) :
    ∃ N : ℕ, AlgebraicCurve.genusFF k F ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (∃ D : AlgebraicCurve.Divisor k F, AlgebraicCurve.Divisor.degree D = (n : ℤ)) →
        (Nat.card k - 1) * Nat.card {D : AlgebraicCurve.Divisor k F //
            0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = (n : ℤ)} =
          Nat.card (AlgebraicCurve.Pic0 k F) *
            (Nat.card k ^ (n + 1 - AlgebraicCurve.genusFF k F) - 1) := by
  obtain ⟨D₀, hfin, hineq, heq⟩ := genus_data (K := k) (E := F) hC
  set g := AlgebraicCurve.genusFF k F with hg
  refine ⟨(Divisor.degree D₀).toNat + g, Nat.le_add_left _ _, ?_⟩
  rintro n hn ⟨D₁, hD₁⟩
  haveI : Finite (Pic0 k F) := Pic0.finite_of_finite k F hC
  have hn' : Divisor.degree D₀ + g ≤ (n : ℤ) := by
    have h1 := Int.self_le_toNat (Divisor.degree D₀)
    have h2 : ((Divisor.degree D₀).toNat : ℤ) + g ≤ n := by exact_mod_cast hn
    linarith
  refine card_eff_degree_eq n D₁ hD₁ _ (fun C₀ => ?_) (fun C₀ => ?_)
  · haveI := hfin (D₁ + (C₀ : Divisor k F))
    exact finite_effCl hC _
  · set C : Divisor k F := D₁ + (C₀ : Divisor k F) with hCdef
    have hdegC : Divisor.degree C = n := by
      rw [hCdef, map_add, hD₁, C₀.2, add_zero]

    haveI := hfin (C - D₀)
    have hpos : 0 < ell (C - D₀) := by
      have := hineq (C - D₀)
      rw [map_sub, hdegC] at this
      have : (0 : ℤ) < ell (C - D₀) := by linarith
      exact_mod_cast this
    obtain ⟨w, hw⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k) (M := LSpace (C - D₀))).mp hpos
    have hf : (w : F) ≠ 0 := fun h => hw (ZeroMemClass.coe_eq_zero.mp h)
    have hle : D₀ ≤ C + pdiv k (w : F) := by
      have h := (mem_lSpace_iff_pdiv hf).mp w.2
      rw [← sub_nonneg]
      rwa [show C + pdiv k (w : F) - D₀ = C - D₀ + pdiv k (w : F) by abel]
    have hell : ell (C + pdiv k (w : F)) = n + 1 - g := by
      have h := heq _ hle
      rw [map_add, degree_pdiv, hdegC, add_zero] at h
      omega
    haveI := hfin (C + pdiv k (w : F))
    rw [card_effCl_congr C hf, card_effCl_mul hC, hell]

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finiteResidue Place Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective HasPrincipalDivisors.exists_divisor LSpace ell mem_lSpace_iff_ord ConstantsAreBase ell_zero_eq_one_of_constantsAreBase genusFF card_effectiveDivisors_mul_eq_sum exists_constantFieldExtension_of_finite card_places_deg_one_eq_sum_divisors_of_constantFieldExtension Pic0.finite_of_finite stichtenothGenusExists_of_isCurveOver Place.ord_eq_zero_of_isAlgebraic indexOfSpecialty_eq_of_genusReached indexOfSpecialty_eq_finrank_H1 finiteDimensional_lSpace"
namespace SchmidtDegOne
p2m_open "AlgebraicCurve"

open PowerSeries

noncomputable def geomP (p : ℕ) (c : ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if p ∣ n then c ^ (n / p) else 0

theorem one_sub_mul_geomP (p : ℕ) (hp : 0 < p) (c : ℚ) :
    (1 - PowerSeries.C (c : ℚ) * PowerSeries.X ^ p) * geomP p c = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
  simp only [geomP, PowerSeries.coeff_mk]
  by_cases hpn : p ≤ n
  · rw [if_pos hpn]
    have hn0 : n ≠ 0 := by omega
    rw [if_neg hn0]
    by_cases hd : p ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hn0
        · exact h
      have h1 : p * m - p = p * (m - 1) := by
        rw [Nat.mul_sub, mul_one]
      rw [if_pos ⟨m, rfl⟩, h1, if_pos ⟨m - 1, rfl⟩, Nat.mul_div_cancel_left _ hp,
        Nat.mul_div_cancel_left _ hp]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    · have hd' : ¬ p ∣ n - p := fun h => hd (by
        have := Nat.dvd_add h (dvd_refl p)
        rwa [Nat.sub_add_cancel hpn] at this)
      rw [if_neg hd, if_neg hd']
      ring
  · rw [if_neg hpn]
    push Not at hpn
    by_cases hn0 : n = 0
    · subst hn0
      simp
    · rw [if_neg hn0, if_neg]
      · ring
      · intro hd
        exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd) (not_le.mpr hpn)

noncomputable def Qpoly (p : ℕ) (R : ℚ) : Polynomial ℚ :=
  (1 - Polynomial.X ^ p) * (1 - Polynomial.C R * Polynomial.X ^ p)

theorem eval_one_Qpoly (p : ℕ) (R : ℚ) : (Qpoly p R).eval 1 = 0 := by
  simp [Qpoly]

theorem rat_lemma (w : ℕ → ℚ) (p N₀ : ℕ) (hp : 0 < p) (hN₀ : p ∣ N₀) (α β R : ℚ)
    (hzero : ∀ n, ¬ p ∣ n → w n = 0) (htail : ∀ m, w (N₀ + p * m) = α * R ^ m - β) :
    ∃ P : Polynomial ℚ, ((Qpoly p R : Polynomial ℚ) : ℚ⟦X⟧) * PowerSeries.mk w = (P : ℚ⟦X⟧) ∧
      P.eval 1 = β * (R - 1) := by
  set H : Polynomial ℚ := PowerSeries.trunc N₀ (PowerSeries.mk w) with hH
  have hdec : PowerSeries.mk w = (H : ℚ⟦X⟧) + PowerSeries.X ^ N₀ *
      (PowerSeries.C α * geomP p R - PowerSeries.C β * geomP p 1) := by
    ext n
    rw [PowerSeries.coeff_mk, map_add, Polynomial.coeff_coe, hH, PowerSeries.coeff_trunc,
      PowerSeries.coeff_X_pow_mul', map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    simp only [geomP, PowerSeries.coeff_mk]
    by_cases hn : n < N₀
    · rw [if_pos hn, if_neg (not_le.mpr hn), add_zero]
    · rw [if_neg hn, if_pos (not_lt.mp hn), zero_add]
      by_cases hd : p ∣ n - N₀
      · rw [if_pos hd, if_pos hd, one_pow, mul_one]
        obtain ⟨m, hm⟩ := hd
        have hn' : n = N₀ + p * m := by omega
        rw [hn', htail, show N₀ + p * m - N₀ = p * m by omega, Nat.mul_div_cancel_left _ hp]
      · rw [if_neg hd, if_neg hd, mul_zero, mul_zero, sub_zero]
        apply hzero
        intro h
        exact hd (Nat.dvd_sub h hN₀)
  have hR := one_sub_mul_geomP p hp R
  have h1 : (1 - PowerSeries.X ^ p) * geomP p 1 = 1 := by
    simpa using one_sub_mul_geomP p hp 1
  refine ⟨Qpoly p R * H + Polynomial.X ^ N₀ *
      (Polynomial.C α * (1 - Polynomial.X ^ p) -
        Polynomial.C β * (1 - Polynomial.C R * Polynomial.X ^ p)), ?_, ?_⟩
  · rw [hdec]
    simp only [Qpoly, Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C]
    linear_combination
      (PowerSeries.X ^ N₀ * PowerSeries.C α * (1 - PowerSeries.X ^ p)) * hR -
        (PowerSeries.X ^ N₀ * PowerSeries.C β *
          (1 - PowerSeries.C R * PowerSeries.X ^ p)) * h1
  · simp [Qpoly, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_pow]
    ring

noncomputable def Eu (f : ℚ⟦X⟧) : ℚ⟦X⟧ := PowerSeries.X * (d⁄dX ℚ) f

theorem coeff_Eu (f : ℚ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (Eu f) = n * PowerSeries.coeff n f := by
  rcases n with _ | m
  · simp [Eu, PowerSeries.coeff_zero_X_mul]
  · rw [Eu, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

theorem Eu_mul (f g : ℚ⟦X⟧) : Eu (f * g) = Eu f * g + f * Eu g := by
  simp only [Eu, Derivation.leibniz, smul_eq_mul]
  ring

theorem Eu_pow (f : ℚ⟦X⟧) (d : ℕ) :
    Eu (f ^ d) = (d : ℚ⟦X⟧) * f ^ (d - 1) * Eu f := by
  simp only [Eu, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  ring

theorem Eu_sub (f g : ℚ⟦X⟧) : Eu (f - g) = Eu f - Eu g := by
  simp only [Eu, map_sub, mul_sub]

theorem eq_zero_of_Eu_eq (𝒩 U : ℚ⟦X⟧) (h𝒩 : PowerSeries.coeff 0 𝒩 = 0)
    (hU : Eu U = 𝒩 * U) (h0 : PowerSeries.coeff 0 U = 0) : U = 0 := by
  suffices hall : ∀ n, PowerSeries.coeff n U = 0 by
    ext n
    rw [map_zero]
    exact hall n
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h0
    · have h := congrArg (PowerSeries.coeff n) hU
      rw [coeff_Eu, PowerSeries.coeff_mul] at h
      have hsum : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
          PowerSeries.coeff x.1 𝒩 * PowerSeries.coeff x.2 U = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        by_cases h2 : x.2 < n
        · rw [ih _ h2, mul_zero]
        · have : x.1 = 0 := by omega
          rw [this, h𝒩, zero_mul]
      rw [hsum] at h
      exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn.ne')

theorem eq_of_Eu_eq (𝒩 V W : ℚ⟦X⟧) (h𝒩 : PowerSeries.coeff 0 𝒩 = 0)
    (hV : Eu V = 𝒩 * V) (hW : Eu W = 𝒩 * W)
    (h0 : PowerSeries.coeff 0 V = PowerSeries.coeff 0 W) : V = W := by
  have := eq_zero_of_Eu_eq 𝒩 (V - W) h𝒩 (by rw [Eu_sub, hV, hW, mul_sub])
    (by rw [map_sub, h0, sub_self])
  exact sub_eq_zero.mp this

theorem Eu_eq_of_rec (a N : ℕ → ℚ) (hN0 : N 0 = 0)
    (ha : ∀ n : ℕ, (n : ℚ) * a n = ∑ r ∈ Finset.Icc 1 n, N r * a (n - r)) :
    Eu (PowerSeries.mk a) = PowerSeries.mk N * PowerSeries.mk a := by
  ext n
  rw [coeff_Eu, PowerSeries.coeff_mk, ha, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), hN0, zero_mul,
    zero_add, Nat.succ_eq_add_one, zero_add, Finset.Ico_add_one_right_eq_Icc]

theorem sum_range_mul_eq (d m : ℕ) (hd : 0 < d) (g : ℕ → ℚ)
    (hg : ∀ i, ¬ d ∣ i → g i = 0) :
    ∑ i ∈ Finset.range (d * m + 1), g i = ∑ r ∈ Finset.range (m + 1), g (d * r) := by
  rw [← Finset.sum_image (f := g) (s := Finset.range (m + 1)) (g := fun r => d * r)
    (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hd h)]
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨r, hr, rfl⟩ := hx
    nlinarith
  · intro x hx hx'
    apply hg
    rintro ⟨r, rfl⟩
    apply hx'
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    exact ⟨r, by nlinarith, rfl⟩

noncomputable def dil (d : ℕ) (a' : ℕ → ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if d ∣ n then a' (n / d) else 0

theorem coeff_dil_mul (d : ℕ) (hd : 0 < d) (a' : ℕ → ℚ) (r : ℕ) :
    PowerSeries.coeff (d * r) (dil d a') = a' r := by
  simp [dil, Nat.mul_div_cancel_left _ hd]

theorem Eu_dil (d : ℕ) (hd : 0 < d) (a' N : ℕ → ℚ) (hN0 : N 0 = 0)
    (hN : ∀ r, ¬ d ∣ r → N r = 0)
    (ha' : ∀ n : ℕ, (n : ℚ) * a' n = ∑ r ∈ Finset.Icc 1 n, N (d * r) * a' (n - r)) :
    Eu (dil d a') = (PowerSeries.C (d : ℚ) * PowerSeries.mk N) * dil d a' := by
  ext n
  rw [coeff_Eu, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul]
  by_cases hdn : d ∣ n
  · obtain ⟨m, rfl⟩ := hdn
    rw [coeff_dil_mul d hd, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_range_mul_eq d m hd _ ?_]
    · have h2 : ∀ r ∈ Finset.range (m + 1),
          PowerSeries.coeff (d * r) (PowerSeries.mk N) *
            PowerSeries.coeff (d * m - d * r) (dil d a') = N (d * r) * a' (m - r) := by
        intro r _
        rw [PowerSeries.coeff_mk, ← Nat.mul_sub, coeff_dil_mul d hd]
      rw [Finset.sum_congr rfl h2, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos m), mul_zero, hN0, zero_mul, zero_add,
        Nat.succ_eq_add_one, zero_add, Finset.Ico_add_one_right_eq_Icc, ← ha']
      push_cast
      ring
    · intro i hi
      simp only [PowerSeries.coeff_mk]
      rw [hN i hi, zero_mul]
  · have hL : PowerSeries.coeff n (dil d a') = 0 := by
      simp [dil, hdn]
    rw [hL, mul_zero]
    symm
    rw [mul_eq_zero]
    right
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h1 : d ∣ x.1
    · have h2 : ¬ d ∣ x.2 := fun h2 => hdn (hx ▸ Nat.dvd_add h1 h2)
      simp [dil, h2]
    · rw [PowerSeries.coeff_mk, hN _ h1, zero_mul]

noncomputable def geo (n : ℕ) : Polynomial ℚ := ∑ i ∈ Finset.range n, Polynomial.X ^ i

theorem eval_one_geo (n : ℕ) : (geo n).eval 1 = n := by
  rw [geo, Polynomial.eval_geom_sum]
  simp

theorem one_sub_X_pow_eq (n : ℕ) :
    (1 : Polynomial ℚ) - Polynomial.X ^ n = (1 - Polynomial.X) * geo n := by
  have := mul_geom_sum (Polynomial.X : Polynomial ℚ) n
  rw [geo]
  linear_combination this

theorem Qpoly_eq (p : ℕ) (R : ℚ) :
    Qpoly p R = (1 - Polynomial.X) * (geo p * (1 - Polynomial.C R * Polynomial.X ^ p)) := by
  rw [Qpoly, one_sub_X_pow_eq]
  ring

theorem one_sub_X_ne_zero : (1 - Polynomial.X : Polynomial ℚ) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp at this

theorem core (d : ℕ) (hd : 0 < d) (A A' N : ℕ → ℚ)
    (hA0 : A 0 = 1) (hA'0 : A' 0 = 1) (hN0 : N 0 = 0)
    (hN : ∀ r, ¬ d ∣ r → N r = 0)
    (hA : ∀ n : ℕ, (n : ℚ) * A n = ∑ r ∈ Finset.Icc 1 n, N r * A (n - r))
    (hA' : ∀ n : ℕ, (n : ℚ) * A' n = ∑ r ∈ Finset.Icc 1 n, N (d * r) * A' (n - r))
    {p₁ N₁ : ℕ} {α₁ β₁ R₁ : ℚ} (hp₁ : 0 < p₁) (hN₁ : p₁ ∣ N₁)
    (hz₁ : ∀ n, ¬ p₁ ∣ n → A n = 0) (ht₁ : ∀ m, A (N₁ + p₁ * m) = α₁ * R₁ ^ m - β₁)
    (hβ₁ : β₁ ≠ 0) (hR₁ : R₁ ≠ 1)
    {p₂ N₂ : ℕ} {α₂ β₂ R₂ : ℚ} (hp₂ : 0 < p₂) (hN₂ : p₂ ∣ N₂)
    (hz₂ : ∀ n, ¬ p₂ ∣ n → A' n = 0) (ht₂ : ∀ m, A' (N₂ + p₂ * m) = α₂ * R₂ ^ m - β₂)
    (hR₂ : R₂ ≠ 1) :
    d = 1 := by

  set Z := PowerSeries.mk A with hZdef
  set 𝒩 := PowerSeries.mk N with h𝒩def
  have hZ : Eu Z = 𝒩 * Z := Eu_eq_of_rec A N hN0 hA
  have hZd : Eu (Z ^ d) = (PowerSeries.C (d : ℚ) * 𝒩) * Z ^ d := by
    rw [Eu_pow, hZ, map_natCast]
    calc (d : ℚ⟦X⟧) * Z ^ (d - 1) * (𝒩 * Z) = d * 𝒩 * (Z ^ (d - 1) * Z) := by ring
      _ = _ := by rw [pow_sub_one_mul hd.ne' Z]
  have hW : Eu (dil d A') = (PowerSeries.C (d : ℚ) * 𝒩) * dil d A' :=
    Eu_dil d hd A' N hN0 hN hA'
  have hWZ : dil d A' = Z ^ d := by
    refine eq_of_Eu_eq (PowerSeries.C (d : ℚ) * 𝒩) _ _ ?_ hW hZd ?_
    · rw [PowerSeries.coeff_C_mul, h𝒩def, PowerSeries.coeff_mk, hN0, mul_zero]
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply (Z ^ d), map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp [dil, hZdef, hA0, hA'0]

  obtain ⟨P₁, hP₁, hev₁⟩ := rat_lemma A p₁ N₁ hp₁ hN₁ α₁ β₁ R₁ hz₁ ht₁
  have hz₂' : ∀ n, ¬ d * p₂ ∣ n → (fun n => if d ∣ n then A' (n / d) else 0) n = 0 := by
    intro n hn
    simp only
    split_ifs with hdn
    · obtain ⟨j, rfl⟩ := hdn
      rw [Nat.mul_div_cancel_left _ hd]
      apply hz₂
      rintro ⟨i, rfl⟩
      exact hn ⟨i, by ring⟩
    · rfl
  have ht₂' : ∀ m, (fun n => if d ∣ n then A' (n / d) else 0) (d * N₂ + d * p₂ * m) =
      α₂ * R₂ ^ m - β₂ := by
    intro m
    simp only
    rw [show d * N₂ + d * p₂ * m = d * (N₂ + p₂ * m) by ring, if_pos ⟨_, rfl⟩,
      Nat.mul_div_cancel_left _ hd, ht₂]
  obtain ⟨P₂, hP₂, hev₂⟩ :
      ∃ P : Polynomial ℚ, ((Qpoly (d * p₂) R₂ : Polynomial ℚ) : ℚ⟦X⟧) * dil d A' =
        (P : ℚ⟦X⟧) ∧ P.eval 1 = β₂ * (R₂ - 1) :=
    rat_lemma _ (d * p₂) (d * N₂) (Nat.mul_pos hd hp₂) (Nat.mul_dvd_mul_left d hN₂)
      α₂ β₂ R₂ hz₂' ht₂'

  have hpoly : Qpoly (d * p₂) R₂ * P₁ ^ d = Qpoly p₁ R₁ ^ d * P₂ := by
    apply Polynomial.coe_inj.mp
    simp only [Polynomial.coe_mul, Polynomial.coe_pow]
    rw [← hP₁, ← hP₂, mul_pow, hWZ]
    ring

  by_contra hd1
  have hd2 : 2 ≤ d := by omega
  have hsplit : (1 - Polynomial.X : Polynomial ℚ) ^ d =
      (1 - Polynomial.X) * (1 - Polynomial.X) ^ (d - 1) := (mul_pow_sub_one hd.ne' _).symm
  have h2 : (1 - Polynomial.X : Polynomial ℚ) *
      (geo (d * p₂) * (1 - Polynomial.C R₂ * Polynomial.X ^ (d * p₂)) * P₁ ^ d) =
      (1 - Polynomial.X) * ((1 - Polynomial.X) ^ (d - 1) *
        (geo p₁ * (1 - Polynomial.C R₁ * Polynomial.X ^ p₁)) ^ d * P₂) := by
    calc _ = Qpoly (d * p₂) R₂ * P₁ ^ d := by rw [Qpoly_eq]; ring
      _ = Qpoly p₁ R₁ ^ d * P₂ := hpoly
      _ = _ := by rw [Qpoly_eq, mul_pow, hsplit]; ring
  have h3 := mul_left_cancel₀ one_sub_X_ne_zero h2
  have h4 := congrArg (Polynomial.eval 1) h3
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C, eval_one_geo, hev₁, hev₂, one_pow, mul_one, sub_self,
    zero_pow (show d - 1 ≠ 0 by omega), zero_mul] at h4
  have hL : ((d * p₂ : ℕ) : ℚ) * (1 - R₂) * (β₁ * (R₁ - 1)) ^ d ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact_mod_cast (Nat.mul_pos hd hp₂).ne'
    · exact sub_ne_zero.mpr (Ne.symm hR₂)
    · exact pow_ne_zero _ (mul_ne_zero hβ₁ (sub_ne_zero.mpr hR₁))
  exact hL h4

section Geometry

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_divisor_degree_eq_one_of_finite.AlgebraicCurve"

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem deg_pos [IsCurveOver K E] (v : Place K E) : 0 < v.deg := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  exact Module.finrank_pos

theorem eq_zero_of_nonneg_of_degree_eq_zero [IsCurveOver K E] (D : Divisor K E) (h0 : 0 ≤ D)
    (hdeg : Divisor.degree D = 0) : D = 0 := by
  classical
  have hsum : Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
    simp [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rw [hsum] at hdeg
  have hnn : ∀ v ∈ D.support, 0 ≤ D v * (v.deg : ℤ) := fun v _ =>
    mul_nonneg (Finsupp.le_def.mp h0 v) (by positivity)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hdeg
  ext v
  by_contra hv
  have hmem : v ∈ D.support := Finsupp.mem_support_iff.mpr hv
  rcases mul_eq_zero.mp (hz v hmem) with h | h
  · exact hv h
  · exact absurd h (by exact_mod_cast (deg_pos v).ne')

variable (K E)

noncomputable def effCount (n : ℕ) : ℕ :=
  Nat.card {D : Divisor K E // 0 ≤ D ∧ Divisor.degree D = (n : ℤ)}

noncomputable def plCount (e : ℕ) : ℕ := Nat.card {v : Place K E | v.deg = e}

noncomputable def NN (r : ℕ) : ℕ := ∑ e ∈ Nat.divisors r, e * plCount K E e

variable {K E}

theorem effCount_zero [IsCurveOver K E] : effCount K E 0 = 1 := by
  unfold effCount
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, le_rfl, by simp⟩, ?_⟩
  rintro ⟨D, hD0, hdeg⟩
  exact Subtype.ext (eq_zero_of_nonneg_of_degree_eq_zero D hD0 (by exact_mod_cast hdeg))

theorem exists_of_effCount_ne_zero {n : ℕ} (h : effCount K E n ≠ 0) :
    ∃ D : Divisor K E, Divisor.degree D = n := by
  obtain ⟨⟨D, -, hD⟩⟩ := (Nat.card_ne_zero.mp h).1
  exact ⟨D, hD⟩

theorem exists_of_plCount_ne_zero {e : ℕ} (h : plCount K E e ≠ 0) :
    ∃ v : Place K E, v.deg = e := by
  obtain ⟨⟨v, hv⟩⟩ := (Nat.card_ne_zero.mp h).1
  exact ⟨v, hv⟩

theorem NN_zero : NN K E 0 = 0 := by simp [NN]

theorem NN_eq_zero_of_not_dvd {d : ℕ} (hdvd : ∀ D : Divisor K E, (d : ℤ) ∣ Divisor.degree D)
    {r : ℕ} (hr : ¬ d ∣ r) : NN K E r = 0 := by
  unfold NN
  refine Finset.sum_eq_zero fun e he => ?_
  rw [Nat.mem_divisors] at he
  by_cases hB : plCount K E e = 0
  · rw [hB, mul_zero]
  · exfalso
    obtain ⟨v, hv⟩ := exists_of_plCount_ne_zero hB
    apply hr
    have h1 : (d : ℤ) ∣ (e : ℤ) := by
      have := hdvd (Finsupp.single v 1)
      rwa [Divisor.degree_single, one_mul, hv] at this
    exact (Int.natCast_dvd_natCast.mp h1).trans he.1

theorem rec_effCount [Finite K] [IsCurveOver K E] [Algebra.EssFiniteType K E] (n : ℕ) :
    (n : ℚ) * (effCount K E n : ℚ) =
      ∑ r ∈ Finset.Icc 1 n, (NN K E r : ℚ) * (effCount K E (n - r) : ℚ) := by
  have := AlgebraicCurve.card_effectiveDivisors_mul_eq_sum K E n
  unfold effCount NN plCount
  exact_mod_cast this

theorem exists_minDeg [IsCurveOver K E] [Nonempty (Place K E)] :
    ∃ d : ℕ, 0 < d ∧ (∃ D : Divisor K E, Divisor.degree D = d) ∧
      ∀ D : Divisor K E, (d : ℤ) ∣ Divisor.degree D := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ D : Divisor K E, Divisor.degree D = n := by
    obtain ⟨v⟩ := ‹Nonempty (Place K E)›
    exact ⟨v.deg, deg_pos v, Finsupp.single v 1, by simp⟩
  obtain ⟨D₀, hD₀⟩ := (Nat.find_spec hex).2
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ⟨D₀, hD₀⟩, fun D => ?_⟩
  set d : ℕ := Nat.find hex with hd
  have hdpos : 0 < d := (Nat.find_spec hex).1
  have hdpos' : (0 : ℤ) < d := by exact_mod_cast hdpos
  set a : ℤ := Divisor.degree D with ha
  by_contra hndvd
  have hr0 : 0 ≤ a % d := Int.emod_nonneg a hdpos'.ne'
  have hrd : a % d < d := Int.emod_lt_of_pos a hdpos'
  have hne : a % d ≠ 0 := fun h => hndvd (Int.dvd_of_emod_eq_zero h)
  have hdeg : Divisor.degree (D - (a / d) • D₀) = a % d := by
    rw [map_sub, map_zsmul, hD₀, smul_eq_mul, Int.emod_def]
    ring
  have h3 : ((a % d).toNat : ℤ) = a % d := Int.toNat_of_nonneg hr0
  have hmin : d ≤ (a % d).toNat :=
    Nat.find_min' hex ⟨by omega, D - (a / d) • D₀, by rw [hdeg, h3]⟩
  omega

theorem hconst_of (hC : ConstantsAreBase K E) :
    ∀ y : E, IsAlgebraic K y → y ∈ (algebraMap K E).range := by
  intro y hy
  have hmem : y ∈ LSpace (0 : Divisor K E) := by
    rw [mem_lSpace_iff_ord]
    exact Or.inr fun v => by simp [Place.ord_eq_zero_of_isAlgebraic v hy]
  rw [hC] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc⟩

theorem ratData (K E : Type*) [Field K] [Finite K] [Field E] [Algebra K E] [IsCurveOver K E]
    [Algebra.EssFiniteType K E] (hC : ConstantsAreBase K E) :
    ∃ (d N₀ : ℕ) (α β R : ℚ), 0 < d ∧ (∃ D : Divisor K E, Divisor.degree D = d) ∧
      (∀ D : Divisor K E, (d : ℤ) ∣ Divisor.degree D) ∧ d ∣ N₀ ∧
      (∀ n, ¬ d ∣ n → (effCount K E n : ℚ) = 0) ∧
      (∀ m, (effCount K E (N₀ + d * m) : ℚ) = α * R ^ m - β) ∧ β ≠ 0 ∧ R ≠ 1 := by
  haveI : PerfectField K := PerfectField.ofFinite
  obtain ⟨hne, -, -⟩ := stichtenothGenusExists_of_isCurveOver (K := K) (F := E) hC
  obtain ⟨d, hd, ⟨D₀, hD₀⟩, hdvd⟩ := exists_minDeg (K := K) (E := E)
  obtain ⟨N, hgN, hL⟩ := AlgebraicCurve.ClassCountFinite.classCount K E hC
  haveI : Finite (Pic0 K E) := Pic0.finite_of_finite K E hC
  set q : ℕ := Nat.card K with hq
  set h : ℕ := Nat.card (Pic0 K E) with hh
  set g : ℕ := genusFF K E with hg
  have hq1 : 1 < q := Finite.one_lt_card
  have hh0 : 0 < h := Nat.card_pos
  have hq1' : (1 : ℚ) < q := by exact_mod_cast hq1
  have hqm : (q : ℚ) - 1 ≠ 0 := sub_ne_zero.mpr hq1'.ne'
  refine ⟨d, d * N, h * (q : ℚ) ^ (d * N + 1 - g) / (q - 1), h / (q - 1), (q : ℚ) ^ d,
    hd, ⟨D₀, hD₀⟩, hdvd, dvd_mul_right d N, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have : effCount K E n = 0 := by
      by_contra hne0
      obtain ⟨D, hD⟩ := exists_of_effCount_ne_zero hne0
      exact hn (Int.natCast_dvd_natCast.mp (hD ▸ hdvd D))
    rw [this, Nat.cast_zero]
  · intro m
    have hNle : N ≤ d * N := Nat.le_mul_of_pos_left N hd
    have hn : N ≤ d * N + d * m := by omega
    have hex : ∃ D : Divisor K E, Divisor.degree D = ((d * N + d * m : ℕ) : ℤ) :=
      ⟨(N + m) • D₀, by rw [map_nsmul, hD₀, nsmul_eq_mul]; push_cast; ring⟩
    have key := hL (d * N + d * m) hn hex
    have hpow : 1 ≤ q ^ (d * N + d * m + 1 - g) := Nat.one_le_pow _ _ (by omega)
    have key' : ((q : ℚ) - 1) * (effCount K E (d * N + d * m) : ℚ) =
        h * ((q : ℚ) ^ (d * N + d * m + 1 - g) - 1) := by
      unfold effCount
      have := congrArg (Nat.cast : ℕ → ℚ) key
      push_cast [Nat.cast_sub hq1.le, Nat.cast_sub hpow] at this
      exact this
    have hexp : d * N + d * m + 1 - g = (d * N + 1 - g) + d * m := by omega
    rw [hexp, pow_add, pow_mul] at key'
    apply mul_left_cancel₀ hqm
    rw [key']
    field_simp
  · exact div_ne_zero (by exact_mod_cast hh0.ne') hqm
  · exact (one_lt_pow₀ hq1' hd.ne').ne'

theorem NN_constantExtension {K : Type*} {K' : Type*} {E : Type*} {E' : Type*}
    [Field K] [Finite K] [Field K'] [Finite K'] [Field E] [Field E']
    [Algebra K K'] [Algebra K' E'] [Algebra K E'] [IsScalarTower K K' E']
    [Algebra K E] [Algebra E E'] [IsScalarTower K E E'] [FiniteDimensional E E']
    [IsCurveOver K E] [Algebra.EssFiniteType K E]
    [IsCurveOver K' E'] [Algebra.EssFiniteType K' E']
    (hC : ConstantsAreBase K E)
    (hgen : Algebra.adjoin E (Set.range (algebraMap K' E')) = ⊤)
    (hC' : ConstantsAreBase K' E') (j : ℕ) (hj : 0 < j) :
    NN K' E' j = NN K E (Module.finrank K K' * j) := by

  obtain ⟨K'', E'', _, _, _, _, _, _, _, _, _, _, _, _, hrank, hgen', hC''⟩ :=
    AlgebraicCurve.exists_constantFieldExtension_of_finite K' E' hC' j hj

  haveI : Algebra.IsIntegral E' E'' := Algebra.IsIntegral.of_finite E' E''
  have h1 : Nat.card {w : Place K'' E'' | w.deg = 1} = NN K' E' j := by
    rw [NN, ← hrank]
    exact AlgebraicCurve.card_places_deg_one_eq_sum_divisors_of_constantFieldExtension
      (k := K') (k' := K'') (F := E') (F' := E'') hgen' (hconst_of hC')

  letI algKK'' : Algebra K K'' := ((algebraMap K' K'').comp (algebraMap K K')).toAlgebra
  letI algKE'' : Algebra K E'' := ((algebraMap E' E'').comp (algebraMap K E')).toAlgebra
  letI algEE'' : Algebra E E'' := ((algebraMap E' E'').comp (algebraMap E E')).toAlgebra
  haveI : IsScalarTower K K' K'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K E' E'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower E E' E'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K K'' E'' := IsScalarTower.of_algebraMap_eq (fun x => by
    show (algebraMap E' E'') (algebraMap K E' x) =
      algebraMap K'' E'' (algebraMap K' K'' (algebraMap K K' x))
    rw [← IsScalarTower.algebraMap_apply K' K'' E'', IsScalarTower.algebraMap_apply K K' E',
      ← IsScalarTower.algebraMap_apply K' E' E''])
  haveI : IsScalarTower K E E'' := IsScalarTower.of_algebraMap_eq (fun x => by
    show (algebraMap E' E'') (algebraMap K E' x) =
      (algebraMap E' E'') (algebraMap E E' (algebraMap K E x))
    rw [← IsScalarTower.algebraMap_apply K E E'])
  haveI : Module.Finite E E'' := Module.Finite.trans E' E''
  haveI : Algebra.IsIntegral E E'' := Algebra.IsIntegral.of_finite E E''
  haveI : FiniteDimensional K K' := Module.finite_of_finrank_pos (by
    rw [Module.finrank_pos_iff]; infer_instance)
  haveI : FiniteDimensional K' K'' := Module.finite_of_finrank_pos (by omega)
  have hrank2 : Module.finrank K K'' = Module.finrank K K' * j := by
    rw [← hrank, Module.finrank_mul_finrank]

  have hgen'' : Algebra.adjoin E (Set.range (algebraMap K'' E'')) = ⊤ := by
    apply eq_top_iff.mpr

    have hE' : (IsScalarTower.toAlgHom E E' E'').range ≤
        Algebra.adjoin E (Set.range (algebraMap K'' E'')) := by
      rw [← Algebra.map_top, ← hgen, AlgHom.map_adjoin]
      apply Algebra.adjoin_mono
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      refine ⟨algebraMap K' K'' c, ?_⟩
      show algebraMap K'' E'' (algebraMap K' K'' c) = algebraMap E' E'' (algebraMap K' E' c)
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

    have hsub : Subring.closure (Set.range (algebraMap E' E'') ∪ Set.range (algebraMap K'' E'')) ≤
        (Algebra.adjoin E (Set.range (algebraMap K'' E''))).toSubring := by
      refine Subring.closure_le.mpr ?_
      rintro y (⟨c, rfl⟩ | hy)
      · exact hE' ⟨c, rfl⟩
      · exact Algebra.subset_adjoin hy
    intro x _
    have hx : x ∈ Algebra.adjoin E' (Set.range (algebraMap K'' E'')) := by
      rw [hgen']; trivial
    rw [Algebra.mem_adjoin_iff] at hx
    exact hsub hx
  have h2 : Nat.card {w : Place K'' E'' | w.deg = 1} = NN K E (Module.finrank K K' * j) := by
    rw [NN, ← hrank2]
    exact AlgebraicCurve.card_places_deg_one_eq_sum_divisors_of_constantFieldExtension
      (k := K) (k' := K'') (F := E) (F' := E'') hgen'' (hconst_of hC)
  rw [← h1, h2]

end Geometry

end AlgebraicCurve.SchmidtDegOne

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_divisor_degree_eq_one_of_finite.AlgebraicCurve AlgebraicCurve.SchmidtDegOne in

theorem solution
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) :
    ∃ D : AlgebraicCurve.Divisor k F, AlgebraicCurve.Divisor.degree D = 1 := by

  obtain ⟨d, N₁, α₁, β₁, R₁, hd, ⟨D₀, hD₀⟩, hdvd, hN₁, hz₁, ht₁, hβ₁, hR₁⟩ := ratData k F hC

  obtain ⟨k', F', _, _, _, _, _, _, _, _, _, _, _, _, hrank, hgen, hC'⟩ :=
    AlgebraicCurve.exists_constantFieldExtension_of_finite k F hC d hd

  obtain ⟨d', N₂, α₂, β₂, R₂, hd', -, -, hN₂, hz₂, ht₂, -, hR₂⟩ := ratData k' F' hC'

  have hNN : ∀ j, NN k' F' j = NN k F (d * j) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [mul_zero, NN_zero, NN_zero]
    · rw [← hrank]
      exact NN_constantExtension hC hgen hC' j hj
  have h1 : d = 1 :=
    core d hd (fun n => (effCount k F n : ℚ)) (fun n => (effCount k' F' n : ℚ))
      (fun r => (NN k F r : ℚ))
      (by simp only [effCount_zero, Nat.cast_one]) (by simp only [effCount_zero, Nat.cast_one])
      (by simp only [NN_zero, Nat.cast_zero])
      (fun r hr => by simp only [NN_eq_zero_of_not_dvd hdvd hr, Nat.cast_zero])
      (rec_effCount (K := k) (E := F))
      (fun n => by simpa only [hNN] using rec_effCount (K := k') (E := F') n)
      hd hN₁ hz₁ ht₁ hβ₁ hR₁ hd' hN₂ hz₂ ht₂ hR₂
  subst h1
  exact ⟨D₀, by simpa using hD₀⟩

end S_AlgebraicCurve_exists_divisor_degree_eq_one_of_finite
end P2MW
export P2MW.S_AlgebraicCurve_exists_divisor_degree_eq_one_of_finite (solution)
