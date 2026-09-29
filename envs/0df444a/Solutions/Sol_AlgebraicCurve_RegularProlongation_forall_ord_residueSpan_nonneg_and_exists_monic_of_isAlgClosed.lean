-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2d98b971-f061-5143-8aaa-9b1e5496370f

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero
import Theorems.Thm_ValuationSubring_exists_mul_pow_inv_mem_of_finiteDimensional_adjoin
import Theorems.Thm_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open AlgebraicCurve IsLocalRing Polynomial

namespace FF39

section ConstHom
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem subtype_comp_eval₂_constHom (R : RegularProlongation A F Fbar) (f : R.integers) :
    (R.integers.subtype : R.integers →+* F).comp (eval₂RingHom (constHom R) f) =
      eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]; exact coe_constHom R a
  · simp

theorem eval₂_mem_integers' (R : RegularProlongation A F Fbar)
    (q : Polynomial A) (f : F) (hf : f ∈ R.integers) :
    Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q ∈ R.integers := by
  have h := congrArg (· q) (subtype_comp_eval₂_constHom R ⟨f, hf⟩)
  simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom] at h
  exact h ▸ (eval₂ (constHom R) ⟨f, hf⟩ q).2

theorem eval₂_mk (R : RegularProlongation A F Fbar) (q : Polynomial A) (f : F) (hf : f ∈ R.integers) :
    (⟨_, eval₂_mem_integers' R q f hf⟩ : R.integers) = eval₂ (constHom R) ⟨f, hf⟩ q := by
  apply Subtype.ext
  have h := congrArg (· q) (subtype_comp_eval₂_constHom R ⟨f, hf⟩)
  simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom] at h
  exact h.symm

theorem residue_comp_eval₂_constHom (R : RegularProlongation A F Fbar) (f : R.integers) :
    (R.residue : R.integers →+* Fbar).comp (eval₂RingHom (constHom R) f) =
      (eval₂RingHom (algebraMap (ResidueField A) Fbar) (R.residue f)).comp
        (Polynomial.mapRingHom (IsLocalRing.residue A)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, coe_mapRingHom, map_C]
    exact R.residue_algebraMap a
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, coe_mapRingHom, Polynomial.map_X]

theorem residue_eval₂' (R : RegularProlongation A F Fbar)
    (q : Polynomial A) (f : F) (hf : f ∈ R.integers) :
    R.residue ⟨_, eval₂_mem_integers' R q f hf⟩ =
      Polynomial.aeval (R.residue ⟨f, hf⟩) (q.map (IsLocalRing.residue A)) := by
  rw [eval₂_mk R q f hf]
  have h := congrArg (· q) (residue_comp_eval₂_constHom R ⟨f, hf⟩)
  simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, coe_mapRingHom] at h
  rw [h, Polynomial.aeval_def, eval₂_map]

end ConstHom

theorem isIntegral_residue_of_mem_T
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (u : F)
    (h₁ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V)
    (huO : ∀ i, u ∈ (R i).integers) (i : ι) :
    IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R i).residue ⟨f, hf i⟩})
      ((R i).residue ⟨u, huO i⟩) := by
  obtain ⟨m, h₂⟩ := ValuationSubring.exists_mul_pow_inv_mem_of_finiteDimensional_adjoin f u h₁
  have h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {f} → (e ∈ V ↔ e ∈ (R i).integers)) → u ∈ V := by
    intro V hV
    obtain ⟨j, hj⟩ := RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed A Fb R hR f hf htr heq i V hV
    rw [hj]; exact huO j
  obtain ⟨p, hpmon, _hpdeg, hpev⟩ :=
    RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring A (R i) ⟨f, hf i⟩ (htr i) u m h₁ h₂ h₃
  exact RegularProlongation.isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero A (R i) ⟨f, hf i⟩ ⟨u, huO i⟩ ⟨p, hpmon, hpev⟩

end FF39
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed.FF39"

open FF39

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    (∀ h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i},
      ∀ i, ∀ w : Place (IsLocalRing.ResidueField A) (Fb i),
        0 ≤ w.ord ((R i).residue ⟨f, hf i⟩) → 0 ≤ w.ord (h i)) ∧
    ∀ h : ∀ i, Fb i, ∃ c : Polynomial (IsLocalRing.ResidueField A), c.Monic ∧
      (fun i => Polynomial.aeval ((R i).residue ⟨f, hf i⟩) c * h i) ∈
        Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} := by
  refine ⟨fun h hh => ?_, fun h => ?_⟩
  ·
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact fun i => hι.elim i

    induction hh using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨u, huO, h₁, hres⟩ := hg
      intro i w hw
      have hint := isIntegral_residue_of_mem_T A Fb R hR f hf htr heq u h₁ huO i
      rw [← hres i]
      exact Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg w hint hw
    | zero => intro i w _; rw [Pi.zero_apply, Place.ord_zero]
    | add a b _ _ ha hb =>
      intro i w hw
      rcases eq_or_ne (a i + b i) 0 with h0 | h0
      · rw [Pi.add_apply, h0, Place.ord_zero]
      rcases eq_or_ne (a i) 0 with ha0 | ha0
      · rw [Pi.add_apply, ha0, zero_add]; exact hb i w hw
      rcases eq_or_ne (b i) 0 with hb0 | hb0
      · rw [Pi.add_apply, hb0, add_zero]; exact ha i w hw
      exact (le_min (ha i w hw) (hb i w hw)).trans
        (by rw [Pi.add_apply]; exact Place.min_ord_le_ord_add w ha0 hb0 h0)
    | smul c a _ ha =>
      intro i w hw
      rcases eq_or_ne c 0 with rfl | hc
      · rw [zero_smul, Pi.zero_apply, Place.ord_zero]
      rw [Pi.smul_apply, Place.ord_smul_of_ne_zero w hc]
      exact ha i w hw
  ·
    obtain ⟨z, hz⟩ := RegularProlongation.exists_forall_residue_eq A Fb R hR h
    have hzO : ∀ i, z ∈ (R i).integers := fun i => (hz i).choose
    have hzres : ∀ i, (R i).residue ⟨z, hzO i⟩ = h i := fun i => (hz i).choose_spec
    obtain ⟨q, hq0, hqT⟩ := ValuationSubring.exists_polynomial_map_residue_ne_zero_eval_mul_mem A f z
    set qbar : Polynomial (IsLocalRing.ResidueField A) := q.map (IsLocalRing.residue A) with hqbar
    have hqbar0 : qbar ≠ 0 := hq0
    set qf : F := Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f q with hqf
    have hqfO : ∀ i, qf ∈ (R i).integers := fun i => eval₂_mem_integers' (R i) q f (hf i)
    have huO : ∀ i, qf * z ∈ (R i).integers := fun i => mul_mem (hqfO i) (hzO i)
    have hures : ∀ i, (R i).residue ⟨qf * z, huO i⟩ =
        Polynomial.aeval ((R i).residue ⟨f, hf i⟩) qbar * h i := by
      intro i
      have heq : (⟨qf * z, huO i⟩ : (R i).integers) = ⟨qf, hqfO i⟩ * ⟨z, hzO i⟩ := rfl
      rw [heq, map_mul, hzres i, hqbar]
      congr 1
      exact residue_eval₂' (R i) q f (hf i)

    have hmem : (fun i => Polynomial.aeval ((R i).residue ⟨f, hf i⟩) qbar * h i) ∈
        Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} :=
      Submodule.subset_span ⟨qf * z, huO, hqT, fun i => hures i⟩

    set lc := qbar.leadingCoeff with hlc
    have hlc0 : lc ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hqbar0
    refine ⟨C lc⁻¹ * qbar, ?_, ?_⟩
    · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact inv_mul_cancel₀ hlc0
    · have heq' : (fun i => aeval ((R i).residue ⟨f, hf i⟩) (C lc⁻¹ * qbar) * h i) =
          lc⁻¹ • (fun i => aeval ((R i).residue ⟨f, hf i⟩) qbar * h i) := by
        funext i
        rw [map_mul, aeval_C, Pi.smul_apply, Algebra.smul_def, mul_assoc]
      rw [heq']
      exact Submodule.smul_mem _ _ hmem

end
end S_AlgebraicCurve_RegularProlongation_forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_forall_ord_residueSpan_nonneg_and_exists_monic_of_isAlgClosed (solution)
