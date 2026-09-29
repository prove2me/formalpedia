-- Prove2me | solution 1 for AlgebraicCurve.card_sub_one_mul_card_effectiveDivisors_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4e87175e-cb1d-5738-a653-fca049256bf1

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Pic0_finite_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_card_sub_one_mul_card_effectiveDivisors_eq
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Divisor Divisor.degree Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective HasPrincipalDivisors.exists_divisor LSpace ell mem_lSpace_iff_ord ConstantsAreBase ell_zero_eq_one_of_constantsAreBase RiemannGenusReachedAt genusFF stichtenothGenusExists_of_isCurveOver RiemannGenusReachedAt.eq_of_ge indexOfSpecialty_eq_of_genusReached indexOfSpecialty_eq_finrank_H1 finiteDimensional_lSpace Pic0.finite_of_finite"
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

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_card_sub_one_mul_card_effectiveDivisors_eq.AlgebraicCurve AlgebraicCurve.ClassCountFinite in

theorem solution
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

end S_AlgebraicCurve_card_sub_one_mul_card_effectiveDivisors_eq
end P2MW
export P2MW.S_AlgebraicCurve_card_sub_one_mul_card_effectiveDivisors_eq (solution)
