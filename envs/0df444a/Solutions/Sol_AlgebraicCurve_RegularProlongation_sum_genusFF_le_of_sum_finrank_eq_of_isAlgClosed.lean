-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f4d8fc27-2270-502e-b1cd-b53602b65562

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_RegularProlongation_span_residue_lSpace_le_residueSpan_inf
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_finrank_residueSpan_inf_add_card_le_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_exists_poleDivisor_of_transcendental
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finiteDimensional_adjoin_residue_of_sum_finrank_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ValuationSubring.coe_toResidueValuationSubring"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation Place Divisor Divisor.degree genusFF IsCurveOver LSpace ell RegularProlongation.span_residue_lSpace_le_residueSpan_inf RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le_of_isAlgClosed RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed RegularProlongation.finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq finiteDimensional_lSpace isCurveOver_of_isAlgClosed_of_transcendental exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental exists_poleDivisor_of_transcendental degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq"
p2m_open "AlgebraicCurve"
namespace RegularProlongation p2m_export "AlgebraicCurve.RegularProlongation" "integers residue span_residue_lSpace_le_residueSpan_inf exists_forall_finrank_residueSpan_inf_add_card_le_of_isAlgClosed exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq finiteDimensional_adjoin_residue_of_sum_finrank_eq" end RegularProlongation
p2m_open_scoped "AlgebraicCurve.RegularProlongation" in
private theorem RegularProlongation.wev
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (D : Divisor L F) (hD : ∀ v : Place L F, D v = max 0 (-v.ord f))
    (Db : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fb i))
    (hDb : ∀ i, ∀ w : Place (IsLocalRing.ResidueField A) (Fb i),
      Db i w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩))) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ell (M • D) + Fintype.card ι ≤ (∑ i, ell (M • Db i)) + 1 := by
  classical
  haveI := hfd

  haveI : IsCurveOver L F := isCurveOver_of_isAlgClosed_of_transcendental f htrL
  obtain ⟨hℓ0, -⟩ := exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental f htrL D hD
  haveI hL0 : FiniteDimensional L ↥(LSpace (0 : Divisor L F)) :=
    Module.finite_of_finrank_pos (by
      change 0 < ell (0 : Divisor L F)
      omega)

  obtain ⟨M₀, hM₀⟩ :=
    RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le_of_isAlgClosed
      A Fb R hR f hf htrL hfd htr heq Db hDb
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨hfin, hcount⟩ := hM₀ M hM

  set ST : Submodule (IsLocalRing.ResidueField A) (∀ i, Fb i) :=
    Submodule.span (IsLocalRing.ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} with hST
  set STM : Submodule (IsLocalRing.ResidueField A) (∀ i, Fb i) :=
    Submodule.span (IsLocalRing.ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          u * (f ^ M)⁻¹ ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} with hSTM
  set ST0 : Submodule (IsLocalRing.ResidueField A) (∀ i, Fb i) :=
    Submodule.span (IsLocalRing.ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} with hST0

  have hlift := RegularProlongation.span_residue_lSpace_le_residueSpan_inf A Fb R f hf hfd D hD M
  haveI : FiniteDimensional L ↥(LSpace (M • D)) := finiteDimensional_lSpace (M • D)
  have hdim := RegularProlongation.finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
    A Fb R hR f hf htr heq (LSpace (M • D))
  have h1 : ell (M • D) ≤ Module.finrank (IsLocalRing.ResidueField A) ↥(ST ⊓ STM) := by
    have := Submodule.finrank_mono (R := IsLocalRing.ResidueField A) hlift
    change Module.finrank L ↥(LSpace (M • D)) ≤ _
    rw [← hdim]
    exact this

  have hle : ST ⊓ ST0 ≤ Submodule.span (IsLocalRing.ResidueField A) {(1 : ∀ i, Fb i)} := by
    intro x hx
    obtain ⟨c, hc⟩ :=
      RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed
        A Fb R hR f hf htrL hfd htr heq x hx.1 hx.2
    have hx' : x = c • (1 : ∀ i, Fb i) := by
      funext i
      simp [hc i, Algebra.algebraMap_eq_smul_one]
    rw [hx']
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  have h2 : Module.finrank (IsLocalRing.ResidueField A) ↥(ST ⊓ ST0) ≤ 1 := by
    calc Module.finrank (IsLocalRing.ResidueField A) ↥(ST ⊓ ST0)
        ≤ Module.finrank (IsLocalRing.ResidueField A)
            ↥(Submodule.span (IsLocalRing.ResidueField A) {(1 : ∀ i, Fb i)}) :=
          Submodule.finrank_mono hle
      _ ≤ ({(1 : ∀ i, Fb i)} : Set (∀ i, Fb i)).toFinset.card := finrank_span_le_card _
      _ = 1 := by simp
  omega
end AlgebraicCurve

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∑ i, genusFF (IsLocalRing.ResidueField A) (Fb i) ≤ genusFF L F := by
  classical
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F := hfd
  haveI hfdᵢ : ∀ i, FiniteDimensional
      (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) := fun i =>
    RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq
      A Fb R hR f hf htr heq i

  obtain ⟨D, hD⟩ := exists_poleDivisor_of_transcendental f htrL
  have hDbex : ∀ i, ∃ Db : Divisor (ResidueField A) (Fb i),
      ∀ w, Db w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩)) := fun i =>
    exists_poleDivisor_of_transcendental ((R i).residue ⟨f, hf i⟩) (htr i)
  choose Db hDb using hDbex

  have hdegD : Divisor.degree D =
      (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F : ℤ) :=
    degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental f htrL D hD
  have hdegDb : ∀ i, Divisor.degree (Db i) =
      (Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) : ℤ) := fun i =>
    degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
      ((R i).residue ⟨f, hf i⟩) (htr i) (Db i) (hDb i)
  have hsumdeg : ∑ i, Divisor.degree (Db i) = Divisor.degree D := by
    simp_rw [hdegDb, hdegD]
    exact_mod_cast congrArg (Nat.cast (R := ℤ)) heq

  obtain ⟨hℓ0F, M₁, -, hRRF⟩ :=
    exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental f htrL D hD
  have hRRᵢ : ∀ i, ∃ Mi : ℕ, 1 ≤ Mi ∧ ∀ N, Mi ≤ N →
        (ell (N • Db i) : ℤ) =
          N * Divisor.degree (Db i) + 1 - genusFF (ResidueField A) (Fb i) := fun i =>
    (exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
      ((R i).residue ⟨f, hf i⟩) (htr i) (Db i) (hDb i)).2
  choose Mᵢ _hMᵢ hRRbᵢ using hRRᵢ

  obtain ⟨M₀, hM₀⟩ := RegularProlongation.wev
    A Fb R hR f hf htrL hfd htr heq D hD Db hDb

  let M : ℕ := max (max M₀ M₁) (Finset.univ.sup Mᵢ)
  have hM0 : M₀ ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hM1 : M₁ ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hMᵢ : ∀ i, Mᵢ i ≤ M := fun i =>
    (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
  have hmain := hM₀ M hM0
  have hmainZ : (ell (M • D) : ℤ) + Fintype.card ι ≤ (∑ i, (ell (M • Db i) : ℤ)) + 1 := by
    exact_mod_cast hmain
  have hlhs : (ell (M • D) : ℤ) = (M : ℤ) * Divisor.degree D + 1 - genusFF L F := hRRF M hM1
  have hrhs : ∑ i, (ell (M • Db i) : ℤ)
      = (M : ℤ) * Divisor.degree D + Fintype.card ι
          - ∑ i, (genusFF (ResidueField A) (Fb i) : ℤ) := by
    calc ∑ i, (ell (M • Db i) : ℤ)
        = ∑ i, ((M : ℤ) * Divisor.degree (Db i) + 1 - genusFF (ResidueField A) (Fb i)) :=
          Finset.sum_congr rfl fun i _ => hRRbᵢ i M (hMᵢ i)
      _ = (M : ℤ) * ∑ i, Divisor.degree (Db i) + ∑ i, (1 : ℤ)
            - ∑ i, (genusFF (ResidueField A) (Fb i) : ℤ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (M : ℤ) * Divisor.degree D + Fintype.card ι
            - ∑ i, (genusFF (ResidueField A) (Fb i) : ℤ) := by
          rw [hsumdeg]; simp
  rw [hlhs, hrhs] at hmainZ
  have hZ : (∑ i, (genusFF (ResidueField A) (Fb i) : ℤ)) ≤ (genusFF L F : ℤ) := by linarith
  exact_mod_cast hZ

end S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed (solution)
