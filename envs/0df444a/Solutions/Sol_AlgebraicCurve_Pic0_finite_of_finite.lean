-- Prove2me | solution 1 for AlgebraicCurve.Pic0.finite_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5df82c67-47b6-54aa-b617-e51c3c39ad9a

import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_finite_setOf_deg_eq
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_finite_of_finite
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_finite_of_finite.AlgebraicCurve"

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "stichtenothGenusExists_of_isCurveOver Place Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic0 Pic0.mk Pic0.mk_surjective IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finiteResidue LSpace ell mem_lSpace_iff_ord ConstantsAreBase Place.finite_setOf_deg_eq" namespace Divisor p2m_export "AlgebraicCurve.Divisor" "degree degree_single degZero mem_degZero principal" end AlgebraicCurve.Divisor
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Divisor" in

private theorem AlgebraicCurve.Divisor.exists_ne_zero_forall_ord_add_nonneg_of_le_degree
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {γ : ℤ} (hγ : ∀ D' : Divisor K F, Divisor.degree D' - (ell D' : ℤ) ≤ γ - 1)
    (D : Divisor K F) (hD : γ ≤ Divisor.degree D) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, 0 ≤ D v + v.ord f := by
  have h1 : 1 ≤ ell D := by
    have := hγ D
    have : (1 : ℤ) ≤ (ell D : ℤ) := by linarith
    exact_mod_cast this
  haveI : Nontrivial (LSpace D) := Module.nontrivial_of_finrank_pos (R := K) h1
  obtain ⟨⟨f, hf⟩, hne⟩ := exists_ne (0 : LSpace D)
  have hf0 : f ≠ 0 := fun h => hne (Subtype.ext h)
  refine ⟨f, hf0, fun v => ?_⟩
  have := (mem_lSpace_iff_ord.mp hf).resolve_left hf0 v
  linarith

theorem solution
    (K F : Type*) [Field K] [Finite K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    Finite (Pic0 K F) := by
  classical
  haveI : PerfectField K := PerfectField.ofFinite
  obtain ⟨⟨P⟩, -, γ, D₀, hR⟩ := AlgebraicCurve.stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hC
  have hγ : ∀ D' : Divisor K F, Divisor.degree D' - (ell D' : ℤ) ≤ γ - 1 := hR.isMax

  have hdegpos : ∀ v : Place K F, 1 ≤ (v.deg : ℤ) := fun v => by
    haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
    have : 0 < v.deg := Module.finrank_pos (R := K) (M := v.ResidueField)
    exact_mod_cast this
  have hPdeg : 0 < (P.deg : ℤ) := lt_of_lt_of_le zero_lt_one (hdegpos P)

  have hterm : ∀ E : Divisor K F, (∀ v, 0 ≤ E v) → ∀ v, E v * v.deg ≤ Divisor.degree E := by
    intro E hE v
    have hdeg : Divisor.degree E = E.sum (fun w n => n * (w.deg : ℤ)) := by
      simp [Divisor.degree, Finsupp.liftAddHom_apply]
    rw [hdeg]
    by_cases hv : v ∈ E.support
    · exact Finset.single_le_sum (f := fun w => E w * (w.deg : ℤ))
        (fun w _ => mul_nonneg (hE w) (by exact_mod_cast (Nat.zero_le _))) hv
    · have : E v = 0 := by simpa [Finsupp.mem_support_iff] using hv
      rw [this, zero_mul]
      exact Finset.sum_nonneg (fun w _ => mul_nonneg (hE w) (by exact_mod_cast (Nat.zero_le _)))

  set m : ℕ := γ.toNat with hm
  set D₁ : Divisor K F := (m : ℤ) • Finsupp.single P 1 with hD₁
  set d : ℤ := Divisor.degree D₁ with hd
  have hd_eq : d = (m : ℤ) * P.deg := by
    simp [hd, hD₁, map_zsmul, Divisor.degree_single]
  have hγd : γ ≤ d := by
    rw [hd_eq]
    calc γ ≤ (m : ℤ) := Int.self_le_toNat γ
      _ = (m : ℤ) * 1 := (mul_one _).symm
      _ ≤ (m : ℤ) * P.deg := by gcongr; omega
  have hd0 : 0 ≤ d := by rw [hd_eq]; positivity

  have hfinPl : {v : Place K F | (v.deg : ℤ) ≤ d}.Finite := by
    have := Set.Finite.biUnion (Finset.range (d.toNat + 1)).finite_toSet
      (fun n _ => AlgebraicCurve.Place.finite_setOf_deg_eq K F n)
    refine this.subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq] at hv
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
    exact ⟨v.deg, by omega, rfl⟩
  let S : Set (Divisor K F) :=
    {E | (∀ v, 0 ≤ E v ∧ E v ≤ d) ∧ ↑E.support ⊆ {v : Place K F | (v.deg : ℤ) ≤ d}}
  have hSfin : S.Finite := by

    let T : Finset (Place K F) := hfinPl.toFinset
    have hST : S ⊆
        {E : Divisor K F | ↑E.support ⊆ (↑T : Set (Place K F)) ∧ ∀ v, 0 ≤ E v ∧ E v ≤ d} := by
      intro E hE
      exact ⟨fun v hv => by simpa [T] using hE.2 hv, hE.1⟩
    refine Set.Finite.subset ?_ hST

    let ι : {E : Divisor K F | ↑E.support ⊆ (↑T : Set (Place K F)) ∧ ∀ v, 0 ≤ E v ∧ E v ≤ d} →
        (T → Set.Icc (0 : ℤ) d) := fun E v => ⟨E.1 v, (E.2.2 v).1, (E.2.2 v).2⟩
    have hι : Function.Injective ι := by
      rintro ⟨E, hE⟩ ⟨E', hE'⟩ h
      ext v
      by_cases hv : v ∈ T
      · have := congrArg (fun g => ((g ⟨v, hv⟩ : Set.Icc (0:ℤ) d) : ℤ)) h
        simpa [ι] using this
      · have h1 : E v = 0 := by
          by_contra hne; exact hv (hE.1 (by simpa [Finsupp.mem_support_iff] using hne))
        have h2 : E' v = 0 := by
          by_contra hne; exact hv (hE'.1 (by simpa [Finsupp.mem_support_iff] using hne))
        simp [h1, h2]
    haveI : Finite (Set.Icc (0 : ℤ) d) := Set.finite_Icc _ _
    exact Set.finite_coe_iff.mp (Finite.of_injective ι hι)

  have hHP : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  have key : ∀ c : Pic0 K F, ∃ E ∈ S, ∃ Dc : Divisor.degZero (K := K) (F := F),
      Pic0.mk Dc = c ∧ ∃ f : F, f ≠ 0 ∧ ∀ v, E v = (Dc : Divisor K F) v + D₁ v + v.ord f := by
    intro c
    obtain ⟨Dc, rfl⟩ := Pic0.mk_surjective c
    have hdeg : γ ≤ Divisor.degree ((Dc : Divisor K F) + D₁) := by
      rw [map_add, Divisor.mem_degZero.1 Dc.2, zero_add]; exact hγd
    obtain ⟨f, hf, hford⟩ :=
      AlgebraicCurve.Divisor.exists_ne_zero_forall_ord_add_nonneg_of_le_degree hγ _ hdeg
    obtain ⟨Df, hDf, hDf0⟩ := hHP.exists_divisor f hf
    refine ⟨(Dc : Divisor K F) + D₁ + Df, ⟨?_, ?_⟩, Dc, rfl, f, hf, fun v => by simp [hDf v]⟩
    ·
      have hEdeg : Divisor.degree ((Dc : Divisor K F) + D₁ + Df) = d := by
        rw [map_add, map_add, Divisor.mem_degZero.1 Dc.2, zero_add, hDf0, add_zero]
      have hnn : ∀ v, 0 ≤ ((Dc : Divisor K F) + D₁ + Df) v := fun v => by
        simpa [hDf v, add_assoc] using hford v
      intro v
      refine ⟨hnn v, ?_⟩
      have h1 := hterm _ hnn v
      rw [hEdeg] at h1
      calc ((Dc : Divisor K F) + D₁ + Df) v
          ≤ ((Dc : Divisor K F) + D₁ + Df) v * v.deg :=
            le_mul_of_one_le_right (hnn v) (hdegpos v)
        _ ≤ d := h1
    · intro v hv
      simp only [Set.mem_setOf_eq]
      have hEdeg : Divisor.degree ((Dc : Divisor K F) + D₁ + Df) = d := by
        rw [map_add, map_add, Divisor.mem_degZero.1 Dc.2, zero_add, hDf0, add_zero]
      have hnn : ∀ v, 0 ≤ ((Dc : Divisor K F) + D₁ + Df) v := fun v => by
        simpa [hDf v, add_assoc] using hford v
      have h1 := hterm _ hnn v
      rw [hEdeg] at h1
      have hne : ((Dc : Divisor K F) + D₁ + Df) v ≠ 0 := by
        simpa [Finsupp.mem_support_iff] using hv
      have hge1 : 1 ≤ ((Dc : Divisor K F) + D₁ + Df) v := by
        have := hnn v; omega
      calc (v.deg : ℤ) = 1 * v.deg := (one_mul _).symm
        _ ≤ ((Dc : Divisor K F) + D₁ + Df) v * v.deg := by
              exact mul_le_mul_of_nonneg_right hge1 (by linarith [hdegpos v])
        _ ≤ d := h1
  choose E hES Dc hDc f hf hE using key
  haveI : Finite S := hSfin.to_subtype
  refine Finite.of_injective (fun c => (⟨E c, hES c⟩ : S)) ?_
  intro c c' h
  have hEE : E c = E c' := congrArg Subtype.val h

  rw [← hDc c, ← hDc c']
  have : ((Dc c : Divisor K F) - (Dc c' : Divisor K F)) ∈ Divisor.principal (K := K) (F := F) := by
    refine ⟨f c' / f c, div_ne_zero (hf c') (hf c), fun v => ?_⟩
    have h1 := hE c v; have h2 := hE c' v
    rw [hEE] at h1
    rw [div_eq_mul_inv, v.ord_mul (hf c') (inv_ne_zero (hf c)), v.ord_inv]
    simp only [Finsupp.coe_sub, Pi.sub_apply]
    linarith

  show (QuotientAddGroup.mk (Dc c) : Pic0 K F) = QuotientAddGroup.mk (Dc c')
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  simpa using this

end S_AlgebraicCurve_Pic0_finite_of_finite
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_finite_of_finite (solution)
