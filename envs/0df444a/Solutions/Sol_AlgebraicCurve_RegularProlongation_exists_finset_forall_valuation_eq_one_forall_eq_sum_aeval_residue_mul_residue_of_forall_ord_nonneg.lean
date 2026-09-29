-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f74bd96c-ab78-51f1-b783-95c433b06c40

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_residue_trace_eq_trace_residue_of_finrank_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span
import Theorems.Thm_Subalgebra_mem_of_isIntegral_of_fg_of_forall_isPrincipal_maximalIdeal_localization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

universe u v

section ReducedBasis

open Polynomial

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

private theorem redint_aeval_ne_zero {f : F} (hf : Transcendental L f) {p : L[X]} (hp : p ≠ 0) :
    aeval f p ≠ 0 := fun h => hp (transcendental_iff.mp hf p h)

private theorem redint_linearIndependent {f : F} (hf : Transcendental L f) {ι : Type*} [Fintype ι]
    (y : ι → F)
    (hyli : ∀ c : ι → L[X], ∑ i, aeval f (c i) * y i = 0 → ∀ i, c i = 0) :
    LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) y := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrep : ∀ i, ∃ (r s : L[X]), s ≠ 0 ∧ (g i : F) * aeval f s = aeval f r := by
    intro i
    obtain ⟨r, s, hrs⟩ :=
      (IntermediateField.mem_adjoin_simple_iff L (α := f) ((g i : F))).mp (g i).2
    by_cases hs : aeval f s = 0
    · exact ⟨0, 1, one_ne_zero, by rw [hrs, hs, div_zero, zero_mul, map_zero]⟩
    · exact ⟨r, s, fun h => hs (by rw [h, map_zero]), by rw [hrs, div_mul_cancel₀ _ hs]⟩
  choose r s hs0 hcl using hrep
  simp only [IntermediateField.smul_def, smul_eq_mul] at hg
  have hsum : (∑ i, aeval f (r i * ∏ l ∈ Finset.univ.erase i, s l) * y i) = 0 := by
    calc ∑ i, aeval f (r i * ∏ l ∈ Finset.univ.erase i, s l) * y i
        = ∑ i, ((g i : F) * y i) * ∏ l, aeval f (s l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, map_prod, ← hcl i,
            ← Finset.mul_prod_erase Finset.univ (fun l => aeval f (s l)) (Finset.mem_univ i)]
          ring
      _ = (∑ i, (g i : F) * y i) * ∏ l, aeval f (s l) := by rw [Finset.sum_mul]
      _ = 0 := by rw [hg, zero_mul]
  intro i
  have hri := hyli _ hsum i
  have hprodne : (∏ l ∈ Finset.univ.erase i, s l) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun l _ => hs0 l
  have hr0 : r i = 0 := by
    rcases mul_eq_zero.mp hri with h | h
    · exact h
    · exact absurd h hprodne
  have hcli := hcl i
  rw [hr0, map_zero] at hcli
  rcases mul_eq_zero.mp hcli with h | h
  · exact Subtype.ext (by simpa using h)
  · exact absurd h (redint_aeval_ne_zero hf (hs0 i))

private theorem redint_isPrincipalIdealRing_adjoin (f : F) :
    IsPrincipalIdealRing (Algebra.adjoin L ({f} : Set F)) := by
  let e : (aeval f : L[X] →ₐ[L] F).range ≃ₐ[L] Algebra.adjoin L ({f} : Set F) :=
    Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval L f).symm
  let g : L[X] →ₐ[L] Algebra.adjoin L ({f} : Set F) := e.toAlgHom.comp (aeval f).rangeRestrict
  have hg : Function.Surjective g := by
    intro w
    obtain ⟨p, hp⟩ : ∃ p : L[X], (aeval f).rangeRestrict p = e.symm w := by
      obtain ⟨p, hp⟩ := (e.symm w).2
      exact ⟨p, Subtype.ext hp⟩
    refine ⟨p, ?_⟩
    show e ((aeval f).rangeRestrict p) = w
    rw [hp]
    exact e.apply_symm_apply w
  exact IsPrincipalIdealRing.of_surjective g.toRingHom hg

open scoped IntermediateField.algebraAdjoinAdjoin in

private theorem redint_exists_aeval_eq_trace (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    {z : F} (hz : IsIntegral (Algebra.adjoin L ({f} : Set F)) z) :
    ∃ p : L[X], aeval f p =
      ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F z :
        IntermediateField.adjoin L ({f} : Set F)) : F) := by
  haveI : IsPrincipalIdealRing (Algebra.adjoin L ({f} : Set F)) := redint_isPrincipalIdealRing_adjoin f
  have htr := Algebra.isIntegral_trace (L := IntermediateField.adjoin L ({f} : Set F)) hz
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral htr
  have hmem : ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F z :
      IntermediateField.adjoin L ({f} : Set F)) : F) ∈ Algebra.adjoin L ({f} : Set F) := by
    rw [← hw, IntermediateField.algebraAdjoinAdjoin.coe_algebraMap]
    exact w.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  exact hmem

private theorem redint_exists_discr_factorization
    {L : Type u} [Field L] [IsAlgClosed L] {F : Type v} [Field F] [Algebra L F] (f : F)
    (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → F)
    (hcard : Fintype.card ι = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hyli : ∀ c : ι → Polynomial L, ∑ i, Polynomial.aeval f (c i) * y i = 0 → ∀ i, c i = 0)
    (hyint : ∀ i, IsIntegral (Algebra.adjoin L ({f} : Set F)) (y i)) :
    ∃ (lead : L) (Cs : Finset L) (m : L → ℕ), lead ≠ 0 ∧
      (Algebra.discr (IntermediateField.adjoin L ({f} : Set F)) y : F)
        = algebraMap L F lead * ∏ c ∈ Cs, (f - algebraMap L F c) ^ m c := by
  classical

  have hli := redint_linearIndependent hf y hyli
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by rw [hcard]; exact Module.finrank_pos)
  let bE : Module.Basis ι (IntermediateField.adjoin L ({f} : Set F)) F :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbE : (bE : ι → F) = y := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hdisc : Algebra.discr (IntermediateField.adjoin L ({f} : Set F)) y ≠ 0 := by
    rw [← hbE]
    exact Algebra.discr_not_zero_of_basis _ bE

  have hyyI : ∀ i j, IsIntegral (Algebra.adjoin L ({f} : Set F)) (y i * y j) :=
    fun i j => (hyint i).mul (hyint j)
  choose tp htp using fun i j => redint_exists_aeval_eq_trace f (hyyI i j)
  set d : L[X] := (Matrix.of tp).det with hd
  have hdiscF : ((Algebra.discr (IntermediateField.adjoin L ({f} : Set F)) y :
      IntermediateField.adjoin L ({f} : Set F)) : F) = aeval f d := by
    rw [Algebra.discr_def, hd]
    rw [show (((Algebra.traceMatrix (IntermediateField.adjoin L ({f} : Set F)) y).det :
        IntermediateField.adjoin L ({f} : Set F)) : F)
        = algebraMap (IntermediateField.adjoin L ({f} : Set F)) F
            (Algebra.traceMatrix (IntermediateField.adjoin L ({f} : Set F)) y).det from rfl,
      RingHom.map_det]
    rw [show aeval f (Matrix.of tp).det = (aeval f : L[X] →ₐ[L] F).toRingHom (Matrix.of tp).det from rfl,
      RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply]
    exact (htp i j).symm
  have hd0 : d ≠ 0 := by
    intro h0
    apply hdisc
    apply (algebraMap (IntermediateField.adjoin L ({f} : Set F)) F).injective
    rw [map_zero]
    exact hdiscF.trans (by rw [h0, map_zero])

  have hsplit : d = C d.leadingCoeff * (d.roots.map (X - C ·)).prod :=
    (IsAlgClosed.splits d).eq_prod_roots
  refine ⟨d.leadingCoeff, d.roots.toFinset, fun c => d.roots.count c, leadingCoeff_ne_zero.mpr hd0, ?_⟩
  rw [hdiscF]
  conv_lhs => rw [hsplit]
  rw [map_mul, aeval_C, map_multiset_prod, Multiset.map_map]
  congr 1
  rw [← Finset.prod_multiset_map_count]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, map_sub, aeval_X, aeval_C]

section Prolongation

variable (A : ValuationSubring L) {Fb : Type v} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
  (R : AlgebraicCurve.RegularProlongation A F Fb)

private theorem redint_exists_lift (p : L[X]) (hp : ∀ n, p.coeff n ∈ A) :
    ∃ p' : A[X], p'.map (algebraMap A L) = p := by
  have hl : p ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨p.coeff n, hp n⟩, rfl⟩
  exact (Polynomial.mem_lifts p).mp hl

private theorem redint_aeval_mem_integers {f : F} (hfR : f ∈ R.integers) (p : L[X])
    (hp : ∀ n, p.coeff n ∈ A) : aeval f p ∈ R.integers := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun n _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem ((R.algebraMap_mem_iff _).mpr (hp n)) (pow_mem hfR n)

private theorem redint_residue_aeval {f : F} (hfR : f ∈ R.integers) (p : A[X]) :
    R.residue ⟨aeval f (p.map (algebraMap A L)), redint_aeval_mem_integers A R hfR _
        (fun n => by rw [coeff_map]; exact (p.coeff n).2)⟩
      = aeval (R.residue ⟨f, hfR⟩) (p.map (IsLocalRing.residue A)) := by

  set ρ : A →+* R.integers :=
    ((algebraMap L F).comp (algebraMap A L)).codRestrict R.integers
      (fun a => (R.algebraMap_mem_iff _).mpr a.2) with hρ
  set fO : R.integers := ⟨f, hfR⟩ with hfO
  have hlhs : (⟨aeval f (p.map (algebraMap A L)), redint_aeval_mem_integers A R hfR _
      (fun n => by rw [coeff_map]; exact (p.coeff n).2)⟩ : R.integers) = p.eval₂ ρ fO := by
    apply Subtype.ext
    show aeval f (p.map (algebraMap A L)) = R.integers.subtype (p.eval₂ ρ fO)
    rw [Polynomial.hom_eval₂, aeval_def, eval₂_map]
    congr 1
  rw [hlhs, Polynomial.hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a
  show R.residue (ρ a) = algebraMap (IsLocalRing.ResidueField A) Fb (IsLocalRing.residue A a)
  exact R.residue_algebraMap a

end Prolongation

end ReducedBasis

private theorem redint_isPrincipal_of_plane_data
    {κ : Type*} [Field κ] {B : Type*} [CommRing B] [IsDomain B] [Algebra κ B]
    (𝔪 : Ideal B) [𝔪.IsMaximal] (z x : B) (c : κ)
    (hz : z ∈ 𝔪) (hx : x - algebraMap κ B c ∈ 𝔪)
    (G : Polynomial (Polynomial κ))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap κ B))).evalEval z x = 0)
    (hG0 : G.evalEval 0 c = 0) (hG' : (Polynomial.derivative G).evalEval 0 c ≠ 0)
    (gens : Set B) (hgens : Algebra.adjoin κ (insert x gens) = ⊤)
    (hrel : ∀ g ∈ gens, ∃ s p : Polynomial (Polynomial κ), s.evalEval 0 c ≠ 0 ∧
      g * (s.map (Polynomial.mapRingHom (algebraMap κ B))).evalEval z x
        = (p.map (Polynomial.mapRingHom (algebraMap κ B))).evalEval z x) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)).IsPrincipal := by
  classical
  set Bm := Localization.AtPrime 𝔪
  let ψ : B →+* Bm := algebraMap B Bm
  let ι : κ →+* B := algebraMap κ B
  let θ : κ →+* Bm := ψ.comp ι
  set I : Ideal Bm := Ideal.span {ψ z}

  have hzmax : ψ z ∈ IsLocalRing.maximalIdeal Bm :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Bm 𝔪 z).mpr hz
  have hImax : I ≤ IsLocalRing.maximalIdeal Bm :=
    (Ideal.span_le).mpr (Set.singleton_subset_iff.mpr hzmax)
  have hxmax : ψ x - θ c ∈ IsLocalRing.maximalIdeal Bm := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff Bm 𝔪 (x - ι c)).mpr hx
    simpa [θ, map_sub] using this

  have hunit : ∀ k : κ, k ≠ 0 → IsUnit (θ k) := fun k hk => (isUnit_iff_ne_zero.mpr hk).map θ

  have hunit_add : ∀ u m : Bm, IsUnit u → m ∈ IsLocalRing.maximalIdeal Bm → IsUnit (u + m) := by
    intro u m hu hm
    by_contra h
    have h1 : u + m ∈ IsLocalRing.maximalIdeal Bm := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
    have h2 : u ∈ IsLocalRing.maximalIdeal Bm := by
      simpa using (IsLocalRing.maximalIdeal Bm).sub_mem h1 hm
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h2) hu

  have hpush : ∀ P : Polynomial (Polynomial κ),
      ψ ((P.map (Polynomial.mapRingHom ι)).evalEval z x)
        = ((P.map (Polynomial.mapRingHom ι)).map (Polynomial.mapRingHom ψ)).evalEval (ψ z) (ψ x) :=
    fun P => (Polynomial.map_mapRingHom_evalEval ψ (P.map (Polynomial.mapRingHom ι)) z x).symm

  have hconst : ∀ P : Polynomial (Polynomial κ),
      ((P.map (Polynomial.mapRingHom ι)).map (Polynomial.mapRingHom ψ)).evalEval 0 (θ c)
        = θ (P.evalEval 0 c) := by
    intro P
    have h1 := Polynomial.map_mapRingHom_evalEval ψ (P.map (Polynomial.mapRingHom ι)) (ι 0) (ι c)
    have h2 := Polynomial.map_mapRingHom_evalEval ι P 0 c
    rw [h2] at h1
    simpa [θ, map_zero] using h1

  have hX : ∀ (P₁ : Polynomial (Polynomial Bm)) (w : Bm),
      P₁.evalEval (ψ z) w - P₁.evalEval 0 w ∈ I := by
    intro P₁ w
    have hd := Polynomial.sub_dvd_eval_sub (ψ z) 0 (Polynomial.eval (Polynomial.C w) P₁)
    rw [sub_zero] at hd
    exact Ideal.mem_span_singleton.mpr hd

  have hY : ∀ (P₁ : Polynomial (Polynomial Bm)) (w w' : Bm),
      w - w' ∣ P₁.evalEval 0 w - P₁.evalEval 0 w' := by
    intro P₁ w w'
    have hd := Polynomial.sub_dvd_eval_sub w w' (P₁.map (Polynomial.evalRingHom 0))
    rwa [Polynomial.map_evalRingHom_eval, Polynomial.map_evalRingHom_eval] at hd

  have hxI : ψ x - θ c ∈ I := by

    set g : Polynomial κ := G.map (Polynomial.evalRingHom 0) with hg
    have hg_c : g.eval c = 0 := by rw [hg, Polynomial.map_evalRingHom_eval]; exact hG0
    have hg'_c : g.derivative.eval c ≠ 0 := by
      rw [hg, Polynomial.derivative_map, Polynomial.map_evalRingHom_eval]; exact hG'

    obtain ⟨g₁, hg₁⟩ : ∃ g₁ : Polynomial κ, g = (Polynomial.X - Polynomial.C c) * g₁ := by
      have := Polynomial.mul_divByMonic_eq_iff_isRoot (p := g) (a := c)
      exact ⟨_, (this.mpr hg_c).symm⟩
    have hg₁c : g₁.eval c = g.derivative.eval c := by
      rw [hg₁]; simp

    set δ : κ := g.derivative.eval c
    obtain ⟨g₂, hg₂⟩ : ∃ g₂ : Polynomial κ,
        g₁ - Polynomial.C δ = (Polynomial.X - Polynomial.C c) * g₂ := by
      have := Polynomial.mul_divByMonic_eq_iff_isRoot (p := g₁ - Polynomial.C δ) (a := c)
      refine ⟨_, (this.mpr ?_).symm⟩
      simp [Polynomial.IsRoot, hg₁c]

    set P₁ := (G.map (Polynomial.mapRingHom ι)).map (Polynomial.mapRingHom ψ) with hP₁
    have hrel0 : P₁.evalEval (ψ z) (ψ x) = 0 := by
      rw [hP₁, ← hpush, hG, map_zero]
    have hmem : P₁.evalEval 0 (ψ x) ∈ I := by
      have := hX P₁ (ψ x)
      rw [hrel0, zero_sub] at this
      have h' := I.neg_mem this
      rwa [neg_neg] at h'

    have hval : ∀ w : Bm, P₁.evalEval 0 w = (g.map θ).eval w := by
      intro w
      rw [← Polynomial.map_evalRingHom_eval]
      congr 1
      rw [hP₁, hg, Polynomial.map_map, Polynomial.map_map, Polynomial.map_map]
      congr 1
      refine Polynomial.ringHom_ext (fun a => ?_) ?_ <;> simp [θ]
    rw [hval] at hmem

    have hgexp : g = (Polynomial.X - Polynomial.C c) *
        (Polynomial.C δ + (Polynomial.X - Polynomial.C c) * g₂) := by
      rw [hg₁, ← hg₂]; ring
    rw [hgexp] at hmem
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hmem

    have hU : IsUnit (θ δ + (ψ x - θ c) * (g₂.map θ).eval (ψ x)) :=
      hunit_add _ _ (hunit δ hg'_c) ((IsLocalRing.maximalIdeal Bm).mul_mem_right _ hxmax)
    exact (Ideal.mul_unit_mem_iff_mem I hU).mp hmem

  have hcong : ∀ P : Polynomial (Polynomial κ),
      ψ ((P.map (Polynomial.mapRingHom ι)).evalEval z x) - θ (P.evalEval 0 c) ∈ I := by
    intro P
    rw [hpush, ← hconst P]
    set P₁ := (P.map (Polynomial.mapRingHom ι)).map (Polynomial.mapRingHom ψ)
    have h1 := hX P₁ (ψ x)
    obtain ⟨r, hr⟩ := hY P₁ (ψ x) (θ c)
    have h2 : P₁.evalEval 0 (ψ x) - P₁.evalEval 0 (θ c) ∈ I := by
      rw [hr]; exact I.mul_mem_right r hxI
    have := I.add_mem h1 h2
    rwa [sub_add_sub_cancel] at this

  let π : Bm →+* Bm ⧸ I := Ideal.Quotient.mk I
  let Pq : Bm → Prop := fun q => ∃ k : κ, π q = π (θ k)
  have hPq_mul : ∀ a b : Bm, Pq a → Pq b → Pq (a * b) := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k * l, by rw [map_mul, map_mul, hk, hl, map_mul]⟩
  have hPq_add : ∀ a b : Bm, Pq a → Pq b → Pq (a + b) := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, by rw [map_add, map_add, hk, hl, map_add]⟩
  have hPq_const : ∀ k : κ, Pq (θ k) := fun k => ⟨k, rfl⟩

  have hPq_of_mul : ∀ (a : Bm) (k l : κ), k ≠ 0 → π a * π (θ k) = π (θ l) → Pq a := by
    intro a k l hk h
    refine ⟨l * k⁻¹, ?_⟩
    have hk' : π (θ k) * π (θ k⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hk, map_one, map_one]
    calc π a = π a * (π (θ k) * π (θ k⁻¹)) := by rw [hk', mul_one]
      _ = π (θ l) * π (θ k⁻¹) := by rw [← mul_assoc, h]
      _ = π (θ (l * k⁻¹)) := by rw [map_mul, map_mul]

  let T : Subalgebra κ B :=
    { carrier := {b | Pq (ψ b)}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul]; exact hPq_mul _ _ ha hb
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [map_one]; simpa using hPq_const 1
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add]; exact hPq_add _ _ ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [map_zero]; simpa using hPq_const 0
      algebraMap_mem' := fun r => by
        simp only [Set.mem_setOf_eq]
        exact hPq_const r }
  have hxT : x ∈ T := ⟨c, Ideal.Quotient.eq.mpr hxI⟩
  have hgensT : gens ⊆ (T : Set B) := by
    intro g hg
    obtain ⟨s, p, hs, hsp⟩ := hrel g hg
    show Pq (ψ g)
    refine hPq_of_mul (ψ g) (s.evalEval 0 c) (p.evalEval 0 c) hs ?_
    have hks' : π (ψ ((s.map (Polynomial.mapRingHom ι)).evalEval z x)) = π (θ (s.evalEval 0 c)) :=
      Ideal.Quotient.eq.mpr (hcong s)
    have hkp' : π (ψ ((p.map (Polynomial.mapRingHom ι)).evalEval z x)) = π (θ (p.evalEval 0 c)) :=
      Ideal.Quotient.eq.mpr (hcong p)
    rw [← hks', ← hkp', ← map_mul, ← map_mul, hsp]
  have hT : ∀ b : B, b ∈ T := by
    intro b
    have hle : Algebra.adjoin κ (insert x gens) ≤ T :=
      Algebra.adjoin_le (Set.insert_subset_iff.mpr ⟨hxT, hgensT⟩)
    rw [hgens] at hle
    exact hle Algebra.mem_top

  have hall : ∀ q : Bm, Pq q := by
    intro q
    obtain ⟨⟨b, u⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl q
    show Pq (IsLocalization.mk' Bm b u)
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine hPq_mul _ _ (hT b) ?_

    obtain ⟨k, hk⟩ := hT (u : B)
    have hk0 : k ≠ 0 := by
      rintro rfl
      have hu : IsUnit (ψ (u : B)) := IsLocalization.map_units Bm u
      have hmem : ψ (u : B) ∈ I := by
        have := Ideal.Quotient.eq.mp hk
        simpa using this
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp (hImax hmem)) hu
    refine hPq_of_mul _ k 1 hk0 ?_
    rw [← hk, ← map_mul, map_one]
    congr 1
    exact (IsLocalization.mk'_spec Bm 1 u).trans (map_one _)

  refine ⟨⟨ψ z, le_antisymm ?_ hImax⟩⟩
  intro m hm
  obtain ⟨k, hk⟩ := hall m
  by_cases hk0 : k = 0
  · subst hk0
    rw [map_zero, map_zero] at hk
    exact Ideal.Quotient.eq_zero_iff_mem.mp hk
  · exfalso
    have hdiff : m - θ k ∈ I := Ideal.Quotient.eq.mp hk
    have hθk : θ k ∈ IsLocalRing.maximalIdeal Bm := by
      simpa using (IsLocalRing.maximalIdeal Bm).sub_mem hm (hImax hdiff)
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hθk) (hunit k hk0)

private def lift_constHom {L : Type u} [Field L] {A : ValuationSubring L} {F : Type v} [Field F]
    [Algebra L F] {Fb : Type v} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : AlgebraicCurve.RegularProlongation A F Fb) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

private theorem redint_exists_lift₂
    {L : Type u} [Field L] (A : ValuationSubring L) (G : Polynomial (Polynomial L))
    (hG : ∀ i j, (G.coeff i).coeff j ∈ A) :
    ∃ GA : Polynomial (Polynomial A),
      GA.map (Polynomial.mapRingHom (algebraMap A L)) = G := by
  have hl : G ∈ Polynomial.lifts (Polynomial.mapRingHom (algebraMap A L)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    have hi : G.coeff i ∈ Polynomial.lifts (algebraMap A L) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro j
      exact ⟨⟨_, hG i j⟩, rfl⟩
    obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp hi
    exact ⟨q, hq⟩
  obtain ⟨GA, hGA⟩ := (Polynomial.mem_lifts _).mp hl
  exact ⟨GA, hGA⟩

private theorem redint_residue_evalEval
    {L : Type u} [Field L] {A : ValuationSubring L} {F : Type v} [Field F] [Algebra L F]
    {Fb : Type v} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : AlgebraicCurve.RegularProlongation A F Fb)
    (GA : Polynomial (Polynomial A)) (a b : F) (ha : a ∈ R.integers) (hb : b ∈ R.integers) :
    ∃ hab : ((GA.map (Polynomial.mapRingHom (algebraMap A L))).map
        (Polynomial.mapRingHom (algebraMap L F))).evalEval a b ∈ R.integers,
      R.residue ⟨_, hab⟩
        = ((GA.map (Polynomial.mapRingHom (IsLocalRing.residue A))).map
            (Polynomial.mapRingHom (algebraMap (IsLocalRing.ResidueField A) Fb))).evalEval
            (R.residue ⟨a, ha⟩) (R.residue ⟨b, hb⟩) := by

  set GO : Polynomial (Polynomial R.integers) :=
    GA.map (Polynomial.mapRingHom (lift_constHom R)) with hGO
  set aO : R.integers := ⟨a, ha⟩
  set bO : R.integers := ⟨b, hb⟩
  have hc1 : (algebraMap L F).comp (algebraMap A L) = R.integers.subtype.comp (lift_constHom R) :=
    RingHom.ext fun x => rfl
  have hc2 : R.residue.comp (lift_constHom R)
      = (algebraMap (IsLocalRing.ResidueField A) Fb).comp (IsLocalRing.residue A) :=
    RingHom.ext fun x => R.residue_algebraMap x
  have hF : (GA.map (Polynomial.mapRingHom (algebraMap A L))).map
      (Polynomial.mapRingHom (algebraMap L F))
      = GO.map (Polynomial.mapRingHom R.integers.subtype) := by
    rw [hGO, Polynomial.map_map, Polynomial.map_map, Polynomial.mapRingHom_comp,
      Polynomial.mapRingHom_comp, hc1]
  have hval : ((GA.map (Polynomial.mapRingHom (algebraMap A L))).map
      (Polynomial.mapRingHom (algebraMap L F))).evalEval a b
      = ((GO.evalEval aO bO : R.integers) : F) := by
    rw [hF]
    exact Polynomial.map_mapRingHom_evalEval R.integers.subtype GO aO bO
  have hmem : ((GA.map (Polynomial.mapRingHom (algebraMap A L))).map
      (Polynomial.mapRingHom (algebraMap L F))).evalEval a b ∈ R.integers := by
    rw [hval]
    exact (GO.evalEval aO bO).2
  refine ⟨hmem, ?_⟩
  have hsub : (⟨_, hmem⟩ : R.integers) = GO.evalEval aO bO := Subtype.ext hval
  rw [hsub, ← Polynomial.map_mapRingHom_evalEval R.residue GO, hGO, Polynomial.map_map,
    Polynomial.map_map, Polynomial.mapRingHom_comp, Polynomial.mapRingHom_comp, hc2]

private theorem redint_residue_evalEval_const
    {L : Type u} [Field L] (A : ValuationSubring L) (GA : Polynomial (Polynomial A)) (a b : A) :
    (GA.map (Polynomial.mapRingHom (IsLocalRing.residue A))).evalEval
        (IsLocalRing.residue A a) (IsLocalRing.residue A b)
      = IsLocalRing.residue A (GA.evalEval a b) := by
  exact Polynomial.map_mapRingHom_evalEval (IsLocalRing.residue A) GA a b

private theorem redint_coe_evalEval
    {L : Type u} [Field L] (A : ValuationSubring L) (GA : Polynomial (Polynomial A)) (a b : A) :
    ((GA.evalEval a b : A) : L)
      = (GA.map (Polynomial.mapRingHom (algebraMap A L))).evalEval (a : L) (b : L) := by
  exact (Polynomial.map_mapRingHom_evalEval (algebraMap A L) GA a b).symm

private theorem redint_isSeparable_of_discr_ne_zero
    {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] [FiniteDimensional K E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (b : ι → E) (hb : Algebra.discr K b ≠ 0) :
    Algebra.IsSeparable K E := by
  by_contra hns
  apply hb
  have htr : Algebra.trace K E = 0 := Algebra.trace_eq_zero_of_not_isSeparable hns
  rw [Algebra.discr_def]
  have hM : Algebra.traceMatrix K b = 0 := by
    ext i j
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, htr]
  rw [hM]
  exact Matrix.det_zero

private theorem redint_residue_discr
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L} {F : Type v} [Field F] [Algebra L F]
    (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    {Fb : Type v} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩))
    (hdeg : Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → F) (hyO : ∀ i, y i ∈ R.integers) :
    ∃ hd : ((Algebra.discr (IntermediateField.adjoin L ({f} : Set F)) y : F)) ∈ R.integers,
      R.residue ⟨_, hd⟩
        = (Algebra.discr (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({R.residue ⟨f, hfR⟩} : Set Fb)) (fun i => R.residue ⟨y i, hyO i⟩) : Fb) := by
  classical
  have hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb := by
    rw [hdeg]; exact Module.finrank_pos

  have hent : ∀ i j, ∃ h : ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F (y i * y j) :
        IntermediateField.adjoin L ({f} : Set F)) : F) ∈ R.integers,
      R.residue ⟨_, h⟩ = ((Algebra.trace (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb (R.residue ⟨y i * y j, mul_mem (hyO i) (hyO j)⟩) :
        IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) : Fb) :=
    fun i j => AlgebraicCurve.RegularProlongation.exists_residue_trace_eq_trace_residue_of_finrank_eq
      A R ⟨f, hfR⟩ htr hfin hdeg.symm ⟨y i * y j, mul_mem (hyO i) (hyO j)⟩
  choose hmem hres using hent

  set MO : Matrix ι ι R.integers := Matrix.of fun i j => (⟨_, hmem i j⟩ : R.integers) with hMO
  have hF : ((Algebra.discr (IntermediateField.adjoin L ({f} : Set F)) y :
      IntermediateField.adjoin L ({f} : Set F)) : F) = ((MO.det : R.integers) : F) := by
    rw [Algebra.discr_def]
    rw [show (((Algebra.traceMatrix (IntermediateField.adjoin L ({f} : Set F)) y).det :
        IntermediateField.adjoin L ({f} : Set F)) : F)
        = algebraMap (IntermediateField.adjoin L ({f} : Set F)) F
            (Algebra.traceMatrix (IntermediateField.adjoin L ({f} : Set F)) y).det from rfl,
      RingHom.map_det]
    rw [show ((MO.det : R.integers) : F) = R.integers.subtype MO.det from rfl, RingHom.map_det]
    congr 1
  have hd : ((Algebra.discr (IntermediateField.adjoin L ({f} : Set F)) y :
      IntermediateField.adjoin L ({f} : Set F)) : F) ∈ R.integers := by
    rw [hF]; exact MO.det.2
  refine ⟨hd, ?_⟩
  have hel : (⟨_, hd⟩ : R.integers) = MO.det := Subtype.ext hF
  rw [hel, RingHom.map_det, Algebra.discr_def]
  rw [show (((Algebra.traceMatrix (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({R.residue ⟨f, hfR⟩} : Set Fb)) (fun i => R.residue ⟨y i, hyO i⟩)).det :
      IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) : Fb)
      = algebraMap (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
          (Algebra.traceMatrix (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({R.residue ⟨f, hfR⟩} : Set Fb)) (fun i => R.residue ⟨y i, hyO i⟩)).det from rfl,
    RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hMO, Matrix.of_apply]
  rw [hres i j]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  rw [← map_mul]
  rfl

private theorem redint_finite_zeros
    {L : Type u} [Field L] [IsAlgClosed L] {F : Type v} [Field F] [Algebra L F] (f : F)
    (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (g : F) (hg : g ≠ 0) : {Q : AlgebraicCurve.Place L F | 0 < Q.ord g}.Finite := by
  haveI : AlgebraicCurve.IsCurveOver L F :=
    AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental f hf
  obtain ⟨P, hP, -⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := L) g hg
  refine (P.support.finite_toSet).subset fun Q hQ => ?_
  have hQ' : 0 < Q.ord g := hQ
  exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (by rw [hP Q]; exact hQ'.ne'))

private theorem redint_mem_iff_ord_nonneg
    {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] (v : AlgebraicCurve.Place K E)
    (g : E) : g ∈ v.toValuationSubring ↔ 0 ≤ v.ord g := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact ⟨fun _ => by simp, fun _ => v.toValuationSubring.zero_mem⟩
  · exact v.mem_iff_ord_nonneg hg

private theorem redint_exists_mul_mem
    {κ : Type*} [Field κ] {E : Type*} [Field E] [Algebra κ E]
    (Mb : Subalgebra κ E) (x : E) (hx : x ∈ Mb) (hxt : Transcendental κ x)
    {ι : Type*} [Fintype ι] (b : ι → E) (hb : ∀ i, b i ∈ Mb)
    (hspan : ∀ u : E, ∃ c : ι → IntermediateField.adjoin κ ({x} : Set E), u = ∑ i, (c i : E) * b i)
    (u : E) : ∃ d ∈ Mb, d ≠ 0 ∧ u * d ∈ Mb := by
  classical
  obtain ⟨c, hc⟩ := hspan u

  have hrep : ∀ i, ∃ (r s : Polynomial κ), s ≠ 0 ∧ (c i : E) * Polynomial.aeval x s = Polynomial.aeval x r := by
    intro i
    obtain ⟨r, s, hrs⟩ :=
      (IntermediateField.mem_adjoin_simple_iff κ (α := x) ((c i : E))).mp (c i).2
    by_cases hs : Polynomial.aeval x s = 0
    · exact ⟨0, 1, one_ne_zero, by rw [hrs, hs, div_zero, zero_mul, map_zero]⟩
    · exact ⟨r, s, fun h => hs (by rw [h, map_zero]), by rw [hrs, div_mul_cancel₀ _ hs]⟩
  choose r s hs0 hcl using hrep

  have haev : ∀ p : Polynomial κ, Polynomial.aeval x p ∈ Mb := by
    intro p
    have hle : Algebra.adjoin κ ({x} : Set E) ≤ Mb :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx)
    apply hle
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  have hane : ∀ {p : Polynomial κ}, p ≠ 0 → Polynomial.aeval x p ≠ 0 :=
    fun hp h => hp (transcendental_iff.mp hxt _ h)
  refine ⟨∏ l, Polynomial.aeval x (s l), Mb.prod_mem fun l _ => haev (s l),
    Finset.prod_ne_zero_iff.mpr fun l _ => hane (hs0 l), ?_⟩
  have hud : u * ∏ l, Polynomial.aeval x (s l)
      = ∑ i, (Polynomial.aeval x (r i) * ∏ l ∈ Finset.univ.erase i, Polynomial.aeval x (s l)) * b i := by
    rw [hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hcl i, ← Finset.mul_prod_erase Finset.univ (fun l => Polynomial.aeval x (s l)) (Finset.mem_univ i)]
    ring
  rw [hud]
  exact Mb.sum_mem fun i _ =>
    Mb.mul_mem (Mb.mul_mem (haev (r i)) (Mb.prod_mem fun l _ => haev (s l))) (hb i)

private theorem redint_adjoin_eq_top
    {κ : Type*} [Field κ] {E : Type*} [CommRing E] [Algebra κ E] (s : Set E) :
    Algebra.adjoin κ ((fun e : Algebra.adjoin κ s => (e : E)) ⁻¹' s) = (⊤ : Subalgebra κ (Algebra.adjoin κ s)) := by
  apply Subalgebra.map_injective (f := (Algebra.adjoin κ s).val) Subtype.val_injective
  rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val]
  congr 1
  ext e
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro he
    exact ⟨⟨e, Algebra.subset_adjoin he⟩, he, rfl⟩

private theorem redint_redsum
    {L : Type u} [Field L] (A : ValuationSubring L) {F : Type v} [Field F] [Algebra L F]
    {Fb : Type v} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : AlgebraicCurve.RegularProlongation A F Fb) {f : F} (hfR : f ∈ R.integers)
    {ι : Type*} [Fintype ι] (y : ι → F) (hyO : ∀ i, y i ∈ R.integers)
    (q : ι → Polynomial L) (hq : ∀ i n, (q i).coeff n ∈ A) :
    ∃ qb : ι → Polynomial (IsLocalRing.ResidueField A),
      ∀ hm : (∑ i, Polynomial.aeval f (q i) * y i) ∈ R.integers,
        R.residue ⟨_, hm⟩
          = ∑ i, Polynomial.aeval (R.residue ⟨f, hfR⟩) (qb i) * R.residue ⟨y i, hyO i⟩ := by
  classical
  choose ql hql using fun i => redint_exists_lift A (q i) (hq i)
  refine ⟨fun i => (ql i).map (IsLocalRing.residue A), fun hm => ?_⟩
  have hterm : ∀ i, Polynomial.aeval f (q i) ∈ R.integers := fun i =>
    redint_aeval_mem_integers A R hfR (q i) (hq i)
  have hsum : (⟨_, hm⟩ : R.integers)
      = ∑ i, ((⟨Polynomial.aeval f (q i), hterm i⟩ : R.integers) * ⟨y i, hyO i⟩) := by
    apply Subtype.ext
    simp
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  have e : (⟨Polynomial.aeval f (q i), hterm i⟩ : R.integers)
      = ⟨Polynomial.aeval f ((ql i).map (algebraMap A L)), redint_aeval_mem_integers A R hfR _
          (fun n => by rw [Polynomial.coeff_map]; exact ((ql i).coeff n).2)⟩ :=
    Subtype.ext (by simp only [hql i])
  rw [e]
  exact redint_residue_aeval A R hfR (ql i)

private theorem redint_span_of_adjoin
    {κ : Type*} [Field κ] {E : Type*} [CommRing E] [Algebra κ E] (x : E)
    {ι : Type*} [Fintype ι] (b : ι → E)
    (t : ι → ι → ι → Polynomial κ) (ht : ∀ i j, b i * b j = ∑ k, Polynomial.aeval x (t i j k) * b k)
    (u : ι → Polynomial κ) (hu : (1 : E) = ∑ k, Polynomial.aeval x (u k) * b k) :
    ∀ m ∈ Algebra.adjoin κ (insert x (Set.range b)),
      ∃ q : ι → Polynomial κ, m = ∑ i, Polynomial.aeval x (q i) * b i := by
  classical
  intro m hm
  refine Algebra.adjoin_induction
    (p := fun m _ => ∃ q : ι → Polynomial κ, m = ∑ i, Polynomial.aeval x (q i) * b i) ?_ ?_ ?_ ?_ hm
  · intro g hg
    rcases Set.mem_insert_iff.mp hg with hgx | ⟨i, hgi⟩
    · refine ⟨fun k => Polynomial.X * u k, ?_⟩
      simp only [map_mul, Polynomial.aeval_X]
      calc g = x * 1 := by rw [hgx, mul_one]
        _ = x * ∑ k, Polynomial.aeval x (u k) * b k := by rw [← hu]
        _ = ∑ k, x * Polynomial.aeval x (u k) * b k := by
          rw [Finset.mul_sum]
          simp only [mul_assoc]
    · refine ⟨Pi.single i 1, ?_⟩
      rw [Finset.sum_eq_single i]
      · simp [← hgi]
      · intro k _ hk
        simp [Pi.single_eq_of_ne hk]
      · intro h
        exact absurd (Finset.mem_univ i) h
  · intro r
    refine ⟨fun k => Polynomial.C r * u k, ?_⟩
    simp only [map_mul, Polynomial.aeval_C]
    calc algebraMap κ E r = algebraMap κ E r * 1 := (mul_one _).symm
      _ = algebraMap κ E r * ∑ k, Polynomial.aeval x (u k) * b k := by rw [← hu]
      _ = ∑ k, algebraMap κ E r * Polynomial.aeval x (u k) * b k := by
        rw [Finset.mul_sum]
        simp only [mul_assoc]
  · rintro a a' _ _ ⟨qa, rfl⟩ ⟨qa', rfl⟩
    exact ⟨qa + qa', by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]⟩
  · rintro a a' _ _ ⟨qa, rfl⟩ ⟨qa', rfl⟩
    refine ⟨fun k => ∑ i, ∑ j, qa i * qa' j * t i j k, ?_⟩
    have key : ∀ i j, (Polynomial.aeval x (qa i) * b i) * (Polynomial.aeval x (qa' j) * b j)
        = ∑ k, Polynomial.aeval x (qa i * qa' j * t i j k) * b k := by
      intro i j
      calc (Polynomial.aeval x (qa i) * b i) * (Polynomial.aeval x (qa' j) * b j)
          = Polynomial.aeval x (qa i) * Polynomial.aeval x (qa' j) * (b i * b j) := by ring
        _ = ∑ k, Polynomial.aeval x (qa i * qa' j * t i j k) * b k := by
          rw [ht i j, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [map_mul]
          ring
    rw [Finset.sum_mul_sum]
    simp_rw [key]
    simp only [map_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

private theorem redint_residue_factorization
    {L : Type u} [Field L] {A : ValuationSubring L} {F : Type v} [Field F] [Algebra L F] {f : F}
    {Fb : Type v} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers)
    {Δ : F} (hΔO : Δ ∈ R.integers) {Δb : Fb} (hΔb : R.residue ⟨Δ, hΔO⟩ = Δb)
    {lead : L} {Cs : Finset L} {m : L → ℕ}
    (hdisc : Δ = algebraMap L F lead * ∏ c ∈ Cs, (f - algebraMap L F c) ^ m c)
    (cA : L → A) (hcA : ∀ c (h : c ∈ A), cA c = ⟨c, h⟩) (hleadA : lead ∈ A) (hCsA : ∀ c ∈ Cs, c ∈ A) :
    Δb = algebraMap (IsLocalRing.ResidueField A) Fb (IsLocalRing.residue A (cA lead)) *
      ∏ c ∈ Cs, (R.residue ⟨f, hfR⟩
        - algebraMap (IsLocalRing.ResidueField A) Fb (IsLocalRing.residue A (cA c))) ^ m c := by
  classical
  let ρ : A →+* R.integers :=
    ((algebraMap L F).comp (algebraMap A L)).codRestrict R.integers
      (fun a => (R.algebraMap_mem_iff _).mpr a.2)
  have hρ : ∀ a : A, R.residue (ρ a)
      = algebraMap (IsLocalRing.ResidueField A) Fb (IsLocalRing.residue A a) :=
    fun a => R.residue_algebraMap a
  have hρcoe : ∀ a : A, ((ρ a : R.integers) : F) = algebraMap L F (a : L) := fun a => rfl
  have hcoe : ∀ c (h : c ∈ A), ((cA c : A) : L) = c := fun c h => by rw [hcA c h]
  have hΔeq : (⟨Δ, hΔO⟩ : R.integers)
      = ρ (cA lead) * ∏ c ∈ Cs, ((⟨f, hfR⟩ : R.integers) - ρ (cA c)) ^ m c := by
    apply Subtype.ext
    show Δ = _
    rw [hdisc]
    push_cast
    simp only [hρcoe, hcoe lead hleadA]
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [hcoe c (hCsA c hc)]
  rw [← hΔb, hΔeq, map_mul, map_prod, hρ]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [map_pow, map_sub, hρ]

private theorem redint_exists_bad_value
    {κ : Type*} [Field κ] {E : Type*} [Field E] [Algebra κ E] (Mb : Subalgebra κ E)
    (𝔪 : Ideal Mb) [𝔪.IsPrime] {Δ x : E} (hΔM : Δ ∈ Mb) (hxM : x ∈ Mb)
    {α : Type*} {Cs : Finset α} {m : α → ℕ} {lead : α} (cb : α → κ)
    (hfact : Δ = algebraMap κ E (cb lead) * ∏ c ∈ Cs, (x - algebraMap κ E (cb c)) ^ m c)
    (hcb_lead : cb lead ≠ 0)
    (hΔm : (⟨Δ, hΔM⟩ : Mb) ∈ 𝔪) :
    ∃ c ∈ Cs, (⟨x, hxM⟩ : Mb) - algebraMap κ Mb (cb c) ∈ 𝔪 := by
  classical
  have hP : 𝔪.IsPrime := inferInstance
  have hΔeq : (⟨Δ, hΔM⟩ : Mb)
      = algebraMap κ Mb (cb lead) * ∏ c ∈ Cs, ((⟨x, hxM⟩ : Mb) - algebraMap κ Mb (cb c)) ^ m c := by
    apply Subtype.ext
    show Δ = _
    rw [hfact]
    push_cast [Subalgebra.coe_algebraMap]
    rfl
  rw [hΔeq] at hΔm
  rcases hP.mem_or_mem hΔm with hl | hp
  · exfalso
    have hu : IsUnit (algebraMap κ Mb (cb lead)) :=
      (isUnit_iff_ne_zero.mpr hcb_lead).map (algebraMap κ Mb)
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem 𝔪 hl hu)
  · obtain ⟨c, hc, hcm⟩ := Ideal.IsPrime.prod_mem_iff.mp hp
    exact ⟨c, hc, hP.mem_of_pow_mem _ hcm⟩

private theorem redint_reduced_radical
    {L : Type u} [Field L] {A : ValuationSubring L} {F : Type v} [Field F] [Algebra L F] {f : F}
    {Fb : Type v} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers)
    (Mb : Subalgebra (IsLocalRing.ResidueField A) Fb) (𝔪 : Ideal Mb) [𝔪.IsPrime]
    (hfbM : R.residue ⟨f, hfR⟩ ∈ Mb)
    {T : Finset (AlgebraicCurve.Place L F)} {z : AlgebraicCurve.Place L F → F}
    (hzO : ∀ Q ∈ T, z Q ∈ R.integers)
    (hzM : ∀ Q (hQ : Q ∈ T), R.residue ⟨z Q, hzO Q hQ⟩ ∈ Mb)
    {N : ℕ} {h : F} (hhO : h ∈ R.integers) (hhM : R.residue ⟨h, hhO⟩ ∈ Mb)
    {c : L} (hcA : c ∈ A)
    (hrad : (∏ Q ∈ T, z Q) ^ N = (f - algebraMap L F c) * h)
    (hcm : (⟨_, hfbM⟩ : Mb) - algebraMap _ Mb (IsLocalRing.residue A ⟨c, hcA⟩) ∈ 𝔪) :
    ∃ Q, ∃ hQ : Q ∈ T, (⟨_, hzM Q hQ⟩ : Mb) ∈ 𝔪 := by
  classical
  have hP : 𝔪.IsPrime := inferInstance
  let zO : T → R.integers := fun Q => ⟨z Q.1, hzO Q.1 Q.2⟩
  let zM : T → Mb := fun Q => ⟨R.residue (zO Q), hzM Q.1 Q.2⟩
  have hcO : algebraMap L F c ∈ R.integers := (R.algebraMap_mem_iff c).mpr hcA

  have hid : (∏ Q : T, zO Q) ^ N = ((⟨f, hfR⟩ : R.integers) - ⟨algebraMap L F c, hcO⟩) * ⟨h, hhO⟩ := by
    apply Subtype.ext
    push_cast
    rw [Finset.prod_coe_sort T z]
    exact hrad

  have hres : (∏ Q : T, R.residue (zO Q)) ^ N
      = (R.residue ⟨f, hfR⟩ - algebraMap (IsLocalRing.ResidueField A) Fb (IsLocalRing.residue A ⟨c, hcA⟩))
          * R.residue ⟨h, hhO⟩ := by
    have := congrArg R.residue hid
    rw [map_pow, map_prod, map_mul, map_sub] at this
    rw [this]
    congr 2
    exact R.residue_algebraMap ⟨c, hcA⟩

  have hidM : (∏ Q : T, zM Q) ^ N
      = ((⟨_, hfbM⟩ : Mb) - algebraMap _ Mb (IsLocalRing.residue A ⟨c, hcA⟩)) * ⟨_, hhM⟩ := by
    apply Subtype.ext
    push_cast [Subalgebra.coe_algebraMap]
    exact hres
  have hmem : (∏ Q : T, zM Q) ^ N ∈ 𝔪 := by
    rw [hidM]
    exact 𝔪.mul_mem_right _ hcm
  obtain ⟨Q, -, hQ⟩ := Ideal.IsPrime.prod_mem_iff.mp (hP.mem_of_pow_mem N hmem)
  exact ⟨Q.1, Q.2, hQ⟩

private theorem redint_coe_evalEval_subalgebra
    {κ : Type*} [CommRing κ] {E : Type*} [CommRing E] [Algebra κ E] (Mb : Subalgebra κ E)
    (P : Polynomial (Polynomial κ)) (a b : Mb) :
    (((P.map (Polynomial.mapRingHom (algebraMap κ Mb))).evalEval a b : Mb) : E)
      = (P.map (Polynomial.mapRingHom (algebraMap κ E))).evalEval (a : E) (b : E) := by
  have h := Polynomial.map_mapRingHom_evalEval (algebraMap Mb E)
    (P.map (Polynomial.mapRingHom (algebraMap κ Mb))) a b
  rw [Polynomial.map_map, Polynomial.mapRingHom_comp, ← IsScalarTower.algebraMap_eq] at h
  exact h.symm

private theorem redint_bad_value_principal
    {L : Type u} [Field L] {A : ValuationSubring L} {F : Type v} [Field F] [Algebra L F] {f : F}
    {Fb : Type v} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers)
    (Mb : Subalgebra (IsLocalRing.ResidueField A) Fb) (𝔪 : Ideal Mb) [𝔪.IsMaximal]
    {ι : Type*} [Fintype ι] (y : ι → F) (hyO : ∀ i, y i ∈ R.integers)
    (hybM : ∀ i, R.residue ⟨y i, hyO i⟩ ∈ Mb) (hfbM : R.residue ⟨f, hfR⟩ ∈ Mb)
    (hMb : Mb = Algebra.adjoin _ (insert (R.residue ⟨f, hfR⟩) (Set.range fun i => R.residue ⟨y i, hyO i⟩)))
    {c : L} (hcA : c ∈ A)
    {zz : F} (hzO : zz ∈ R.integers) (hzM : R.residue ⟨zz, hzO⟩ ∈ Mb) (hzm : (⟨_, hzM⟩ : Mb) ∈ 𝔪)
    (hcm : (⟨_, hfbM⟩ : Mb) - algebraMap _ Mb (IsLocalRing.residue A ⟨c, hcA⟩) ∈ 𝔪)
    (G : Polynomial (Polynomial L)) (hGA : ∀ n k, (G.coeff n).coeff k ∈ A)
    (hGrel : (G.map (Polynomial.mapRingHom (algebraMap L F))).evalEval zz f = 0)
    (hG0 : G.evalEval 0 c = 0)
    (hδA : (Polynomial.derivative G).evalEval 0 c ∈ A)
    (hδres : IsLocalRing.residue A ⟨_, hδA⟩ ≠ 0)
    (s p : ι → Polynomial (Polynomial L))
    (hsA : ∀ i n k, ((s i).coeff n).coeff k ∈ A) (hpA : ∀ i n k, ((p i).coeff n).coeff k ∈ A)
    (hsid : ∀ i, y i * ((s i).map (Polynomial.mapRingHom (algebraMap L F))).evalEval zz f
      = ((p i).map (Polynomial.mapRingHom (algebraMap L F))).evalEval zz f)
    (hs0A : ∀ i, (s i).evalEval 0 c ∈ A) (hsres : ∀ i, IsLocalRing.residue A ⟨_, hs0A i⟩ ≠ 0) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)).IsPrincipal := by
  classical
  subst hMb
  obtain ⟨GA, hGA'⟩ := redint_exists_lift₂ A G hGA

  have hGA0 : GA.evalEval 0 ⟨c, hcA⟩ = 0 := by
    apply Subtype.ext
    rw [redint_coe_evalEval, hGA']
    simpa using hG0
  have hGAδ : (Polynomial.derivative GA).evalEval 0 ⟨c, hcA⟩ = ⟨_, hδA⟩ := by
    apply Subtype.ext
    rw [redint_coe_evalEval, ← Polynomial.derivative_map, hGA']
    simp
  refine redint_isPrincipal_of_plane_data 𝔪 ⟨_, hzM⟩ ⟨_, hfbM⟩ (IsLocalRing.residue A ⟨c, hcA⟩) hzm hcm
    (GA.map (Polynomial.mapRingHom (IsLocalRing.residue A))) ?_ ?_ ?_
    {g | (g : Fb) ∈ insert (R.residue ⟨f, hfR⟩) (Set.range fun i => R.residue ⟨y i, hyO i⟩)} ?_ ?_
  ·
    apply Subtype.ext
    rw [redint_coe_evalEval_subalgebra, ZeroMemClass.coe_zero]
    obtain ⟨hab, hab'⟩ := redint_residue_evalEval R GA zz f hzO hfR
    rw [← hab']
    have h0 : (⟨_, hab⟩ : R.integers) = 0 := by
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero]
      show ((GA.map (Polynomial.mapRingHom (algebraMap A L))).map
        (Polynomial.mapRingHom (algebraMap L F))).evalEval zz f = 0
      rw [hGA']
      exact hGrel
    rw [h0, map_zero]
  ·
    have h := redint_residue_evalEval_const A GA 0 ⟨c, hcA⟩
    rw [map_zero] at h
    rw [h, hGA0, map_zero]
  ·
    rw [Polynomial.derivative_map]
    have h := redint_residue_evalEval_const A (Polynomial.derivative GA) 0 ⟨c, hcA⟩
    rw [map_zero] at h
    rw [h, hGAδ]
    exact hδres
  ·
    have h14 := redint_adjoin_eq_top (κ := IsLocalRing.ResidueField A)
      (insert (R.residue ⟨f, hfR⟩) (Set.range fun i => R.residue ⟨y i, hyO i⟩))
    refine top_unique ?_
    rw [← h14]
    exact Algebra.adjoin_mono (Set.subset_insert _ _)
  ·
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hgf | ⟨i, hgi⟩
    · refine ⟨1, Polynomial.X, by simp, ?_⟩
      have : g = ⟨_, hfbM⟩ := Subtype.ext hgf
      rw [this]
      simp
    · obtain ⟨sA, hsA'⟩ := redint_exists_lift₂ A (s i) (hsA i)
      obtain ⟨pA, hpA'⟩ := redint_exists_lift₂ A (p i) (hpA i)
      refine ⟨sA.map (Polynomial.mapRingHom (IsLocalRing.residue A)),
        pA.map (Polynomial.mapRingHom (IsLocalRing.residue A)), ?_, ?_⟩
      · have h := redint_residue_evalEval_const A sA 0 ⟨c, hcA⟩
        rw [map_zero] at h
        rw [h]
        have hs : sA.evalEval 0 ⟨c, hcA⟩ = ⟨_, hs0A i⟩ := by
          apply Subtype.ext
          rw [redint_coe_evalEval, hsA']
          simp
        rw [hs]
        exact hsres i
      · apply Subtype.ext
        rw [Subalgebra.coe_mul, redint_coe_evalEval_subalgebra, redint_coe_evalEval_subalgebra]
        obtain ⟨habs, habs'⟩ := redint_residue_evalEval R sA zz f hzO hfR
        obtain ⟨habp, habp'⟩ := redint_residue_evalEval R pA zz f hzO hfR
        rw [← habs', ← habp']
        have hg' : (g : Fb) = R.residue ⟨y i, hyO i⟩ := hgi.symm
        rw [hg', ← map_mul]
        congr 1
        apply Subtype.ext
        push_cast
        simp only [hsA', hpA']
        exact hsid i

private theorem redint_span_eq_top
    {κ : Type*} [Field κ] {E : Type*} [Field E] [Algebra κ E] (x : E) {ι : Type*} [Fintype ι] (b : ι → E)
    (hspan : ∀ u : E, ∃ c : ι → IntermediateField.adjoin κ ({x} : Set E), u = ∑ i, (c i : E) * b i) :
    Submodule.span (IntermediateField.adjoin κ ({x} : Set E)) (Set.range b) = ⊤ := by
  refine eq_top_iff.mpr fun u _ => ?_
  obtain ⟨c, hc⟩ := hspan u
  rw [hc]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : (c i : E) * b i = c i • b i := by rw [Algebra.smul_def]; rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem redint_isIntegral_of_le
    {κ : Type*} [CommRing κ] {E : Type*} [CommRing E] [Algebra κ E] {S₁ S₂ : Subalgebra κ E}
    (h : S₁ ≤ S₂) {u : E} (hu : IsIntegral S₁ u) : IsIntegral S₂ u := by
  obtain ⟨p, hpm, hp⟩ := hu
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, hpm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (algebraMap S₂ E).comp (Subalgebra.inclusion h).toRingHom = algebraMap S₁ E :=
    RingHom.ext fun a => rfl
  rw [this]
  exact hp

section Seven

open Polynomial

section Device

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

private theorem redint_exists_aeval_eq_discr (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → F)
    (hyint : ∀ i, IsIntegral (Algebra.adjoin L ({f} : Set F)) (y i)) :
    ∃ d : L[X], ((Algebra.discr (IntermediateField.adjoin L ({f} : Set F)) y :
      IntermediateField.adjoin L ({f} : Set F)) : F) = aeval f d := by
  classical
  have hyyI : ∀ i j, IsIntegral (Algebra.adjoin L ({f} : Set F)) (y i * y j) :=
    fun i j => (hyint i).mul (hyint j)
  choose tp htp using fun i j => redint_exists_aeval_eq_trace f (hyyI i j)
  refine ⟨(Matrix.of tp).det, ?_⟩
  rw [Algebra.discr_def]
  rw [show (((Algebra.traceMatrix (IntermediateField.adjoin L ({f} : Set F)) y).det :
      IntermediateField.adjoin L ({f} : Set F)) : F)
      = algebraMap (IntermediateField.adjoin L ({f} : Set F)) F
          (Algebra.traceMatrix (IntermediateField.adjoin L ({f} : Set F)) y).det from rfl,
    RingHom.map_det]
  rw [show aeval f (Matrix.of tp).det = (aeval f : L[X] →ₐ[L] F).toRingHom (Matrix.of tp).det from rfl,
    RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply]
  exact (htp i j).symm

end Device

section Span

variable {E : Type*} [Field E] {A : Type*} [CommRing A] [Algebra A E] {ι : Type*}

private theorem redint_mul_mem_span (b : ι → E)
    (hmul : ∀ i j, b i * b j ∈ Submodule.span A (Set.range b)) :
    ∀ u v : E, u ∈ Submodule.span A (Set.range b) → v ∈ Submodule.span A (Set.range b) →
      u * v ∈ Submodule.span A (Set.range b) := by
  intro u v hu hv
  have h := Submodule.mul_mem_mul hu hv
  rw [Submodule.span_mul_span] at h
  refine (Submodule.span_le.mpr ?_) h
  rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  exact hmul i j

private theorem redint_isIntegral_of_mem_span [Fintype ι] (b : ι → E)
    (hone : (1 : E) ∈ Submodule.span A (Set.range b))
    (hmul : ∀ i j, b i * b j ∈ Submodule.span A (Set.range b)) {e : E}
    (he : e ∈ Submodule.span A (Set.range b)) : IsIntegral A e :=
  IsIntegral.of_mem_of_fg
    ((Submodule.span A (Set.range b)).toSubalgebra hone (redint_mul_mem_span b hmul))
    (Submodule.fg_span (Set.finite_range b)) e he

end Span

private theorem redint_prime_eq_maximalIdeal {A : Type*} [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] {T : Type*} [CommRing T] [IsDomain T] [Algebra A T]
    [Algebra.IsIntegral A T] (𝔪 : Ideal T) [𝔪.IsMaximal] (P : Ideal (Localization.AtPrime 𝔪))
    (hP0 : P ≠ ⊥) (hP : P.IsPrime) : P = IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) := by
  let Q : Ideal T := P.comap (algebraMap T (Localization.AtPrime 𝔪))
  haveI hQ : Q.IsPrime := Ideal.IsPrime.comap _
  have hPQ : Q.map (algebraMap T (Localization.AtPrime 𝔪)) = P :=
    IsLocalization.map_under 𝔪.primeCompl (Localization.AtPrime 𝔪) P
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hP0
    rw [← hPQ, h, Ideal.map_bot]
  have hQle : Q ≤ 𝔪 := by
    intro n hn
    by_contra hn𝔪
    have hu := IsLocalization.map_units (Localization.AtPrime 𝔪) (⟨n, hn𝔪⟩ : 𝔪.primeCompl)
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hn hu)
  obtain ⟨n₀, hn₀Q, hn₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  have hcne : Q.comap (algebraMap A T) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hn₀ hn₀Q (Algebra.IsIntegral.isIntegral n₀)
  haveI : (Q.comap (algebraMap A T)).IsPrime := Ideal.IsPrime.comap _
  have hcmax : (Q.comap (algebraMap A T)).IsMaximal := IsPrime.to_maximal_ideal hcne
  have hQmax : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q hcmax
  have hQ𝔪 : Q = 𝔪 := hQmax.eq_of_le (Ideal.IsMaximal.ne_top ‹𝔪.IsMaximal›) hQle
  rw [← hPQ, hQ𝔪]
  exact Localization.AtPrime.map_eq_maximalIdeal

section Order

variable {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {E : Type*} [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E] [FiniteDimensional K E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem redint_mem_span_of_isIntegral (b : ι → E)
    (hone : (1 : E) ∈ Submodule.span R (Set.range b))
    (hprod : ∀ i j, b i * b j ∈ Submodule.span R (Set.range b))
    (hli : LinearIndependent K b) (htop : Submodule.span K (Set.range b) = ⊤)
    (hd : ∃ d : R, IsUnit d ∧ algebraMap R K d = Algebra.discr K b) :
    ∀ e : E, IsIntegral R e → e ∈ Submodule.span R (Set.range b) := by
  classical
  obtain ⟨d, hdu, hdK⟩ := hd
  let S : Subalgebra R E :=
    (Submodule.span R (Set.range b)).toSubalgebra hone (redint_mul_mem_span b hprod)
  have hbS : ∀ i, b i ∈ S := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hliR : LinearIndependent R b := by
    refine hli.restrict_scalars ?_
    intro r s hrs
    apply IsFractionRing.injective R K
    simpa [Algebra.smul_def] using hrs
  let v : ι → S := fun i => ⟨b i, hbS i⟩
  let bS : Module.Basis ι R S := Module.Basis.mk (v := v)
    (LinearIndependent.of_comp (AlgHom.toLinearMap S.val) hliR) (by
      intro s _
      have hs : (s : E) ∈ Submodule.span R (Set.range b) := s.2
      have hrange : Set.range b = (AlgHom.toLinearMap S.val) '' Set.range v := by
        ext e
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨v i, ⟨i, rfl⟩, rfl⟩
        · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
      rw [hrange, ← Submodule.map_span] at hs
      obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp hs
      have hteq : t = s := Subtype.ext hts
      exact hteq ▸ ht)
  have hStop : Submodule.span K ((S : Subalgebra R E) : Set E) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← htop]
    exact Submodule.span_mono (Set.range_subset_iff.mpr hbS)
  have hRE : ∀ r : R, r ≠ 0 → algebraMap R E r ≠ 0 := by
    intro r hr h0
    rw [IsScalarTower.algebraMap_apply R K E] at h0
    exact hr ((map_eq_zero_iff _ (IsFractionRing.injective R K)).mp
      ((map_eq_zero_iff _ (algebraMap K E).injective).mp h0))

  haveI hEloc : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) E := by
    refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨_, r, hr, rfl⟩
      refine isUnit_iff_ne_zero.mpr ?_
      rw [← IsScalarTower.algebraMap_apply R S E r]
      exact hRE r (nonZeroDivisors.ne_zero hr)
    · intro z
      have hz : z ∈ Submodule.span K (Set.range b) := by
        rw [htop]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hz
      obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ c
      choose a ha using fun i => hr i (Finset.mem_univ i)
      have hw : (∑ i, a i • b i) ∈ Submodule.span R (Set.range b) :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      refine ⟨(⟨∑ i, a i • b i, hw⟩, ⟨algebraMap R S r, r, r.2, rfl⟩), ?_⟩
      show z * algebraMap S E (algebraMap R S r) = ∑ i, a i • b i
      rw [← IsScalarTower.algebraMap_apply R S E, ← hc, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul K (a i) (b i), ha i, smul_assoc, Algebra.smul_def, mul_comm]
      exact (Algebra.smul_def _ _).symm
    · intro s t hst
      exact ⟨1, by rw [Subtype.ext (hst : (s : E) = t)]⟩

  have hdisc : algebraMap R K (Algebra.discr R bS) = Algebra.discr K b := by
    rw [← Algebra.discr_localizationLocalization R (nonZeroDivisors R) E bS]
    have hfun : ⇑(bS.localizationLocalization K (nonZeroDivisors R) E) = b := by
      funext i
      rw [Module.Basis.localizationLocalization_apply, Module.Basis.mk_apply]
      rfl
    rw [hfun]
  have hdeq : Algebra.discr R bS = d := IsFractionRing.injective R K (hdisc.trans hdK.symm)
  have hIC : integralClosure R E ≤ S :=
    Algebra.integralClosure_le_of_isUnit_discr_of_span_eq_top S hStop bS (hdeq ▸ hdu)
  intro e he
  exact hIC (show e ∈ integralClosure R E from he)

end Order

private theorem redint_isIntegral_of_isIntegral_subalgebra {κ : Type*} [Field κ] {E : Type*} [Field E]
    [Algebra κ E] {R : Type*} [CommRing R] [Algebra R E] (Mb : Subalgebra κ E)
    (hMb : ∀ n : Mb, IsIntegral R (n : E)) {w : E} (hw : IsIntegral Mb w) : IsIntegral R w := by
  let φ : Mb →+* integralClosure R E := (algebraMap Mb E).codRestrict _ fun n => hMb n
  have hwC : IsIntegral (integralClosure R E) w := by
    obtain ⟨p, hpm, hp⟩ := hw
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [eval₂_map]
    have hcomp : (algebraMap (integralClosure R E) E).comp φ = algebraMap Mb E :=
      RingHom.ext fun n => rfl
    rw [hcomp]
    exact hp
  exact isIntegral_trans w hwC

private theorem redint_exists_mul_mem_span {A : Type*} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    {Rₚ : Type*} [CommRing Rₚ] [Algebra A Rₚ] [IsLocalization.AtPrime Rₚ 𝔭]
    {E : Type*} [CommRing E] [Algebra A E] [Algebra Rₚ E]
    (hcomp : ∀ a : A, algebraMap Rₚ E (algebraMap A Rₚ a) = algebraMap A E a)
    {ι : Type*} [Fintype ι] (b : ι → E) {w : E} (hw : w ∈ Submodule.span Rₚ (Set.range b)) :
    ∃ u : 𝔭.primeCompl, algebraMap A E u * w ∈ Submodule.span A (Set.range b) := by
  classical
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hw
  obtain ⟨u, hu⟩ := IsLocalization.exist_integer_multiples 𝔭.primeCompl Finset.univ r
  choose a ha using fun i => hu i (Finset.mem_univ i)
  refine ⟨u, ?_⟩
  have hcalc : algebraMap A E u * w = ∑ i, a i • b i := by
    rw [← hr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, ← hcomp (a i), ha i, Algebra.smul_def, map_mul, hcomp,
      mul_assoc]
  rw [hcalc]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem redint_isIntegrallyClosed_atPrime {κ : Type*} [Field κ] {E : Type*} [Field E]
    [Algebra κ E] (Mb : Subalgebra κ E) (𝔪 : Ideal Mb) [𝔪.IsMaximal]
    (hfrac : ∀ z : E, ∃ d ∈ Mb, d ≠ 0 ∧ z * d ∈ Mb)
    (hint : ∀ w : E, IsIntegral Mb w → ∃ (n : Mb) (u : 𝔪.primeCompl), w * ((u : Mb) : E) = n) :
    IsIntegrallyClosed (Localization.AtPrime 𝔪) := by
  haveI : IsDomain (Localization.AtPrime 𝔪) :=
    IsLocalization.isDomain_of_local_atPrime (Ideal.IsMaximal.isPrime ‹𝔪.IsMaximal›)
  have hne : ∀ y : 𝔪.primeCompl, ((y : Mb) : E) ≠ 0 := by
    intro y h0
    apply y.2
    have hy0 : (y : Mb) = 0 := Subtype.ext h0
    rw [hy0]
    exact 𝔪.zero_mem
  have hunits : ∀ y : 𝔪.primeCompl, IsUnit (algebraMap Mb E y) := fun y =>
    isUnit_iff_ne_zero.mpr (hne y)
  letI algBE : Algebra (Localization.AtPrime 𝔪) E := (IsLocalization.lift hunits).toAlgebra
  haveI : @IsScalarTower Mb (Localization.AtPrime 𝔪) E Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun m => (IsLocalization.lift_eq hunits m).symm
  have hBMb : ∀ n : Mb,
      algebraMap (Localization.AtPrime 𝔪) E (algebraMap Mb (Localization.AtPrime 𝔪) n) = (n : E) :=
    fun n => (IsScalarTower.algebraMap_apply Mb (Localization.AtPrime 𝔪) E n).symm
  haveI : IsFractionRing Mb E := by
    refine IsFractionRing.of_field Mb E fun z => ?_
    obtain ⟨d, hdM, hd0, hzd⟩ := hfrac z
    refine ⟨⟨z * d, hzd⟩, ⟨d, hdM⟩, ?_⟩
    change z = (z * d) / d
    rw [mul_div_assoc, div_self hd0, mul_one]
  haveI : IsFractionRing (Localization.AtPrime 𝔪) E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔪.primeCompl
      (Localization.AtPrime 𝔪) E
  rw [isIntegrallyClosed_iff E]
  intro z hz
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization 𝔪.primeCompl z hz
  obtain ⟨n, u, hnu⟩ := hint _ hm
  refine ⟨IsLocalization.mk' (Localization.AtPrime 𝔪) n (m * u), ?_⟩
  apply mul_right_cancel₀ (hne (m * u))
  have h1 := congrArg (algebraMap (Localization.AtPrime 𝔪) E)
    (IsLocalization.mk'_spec (Localization.AtPrime 𝔪) n (m * u))
  rw [map_mul, hBMb, hBMb] at h1
  rw [h1, ← hnu, Submonoid.smul_def, Algebra.smul_def, Submonoid.coe_mul, Subalgebra.coe_mul,
    show algebraMap Mb E (m : Mb) = ((m : Mb) : E) from rfl]
  ring

open scoped IntermediateField.algebraAdjoinAdjoin in

private theorem redint_isPrincipal_of_discr_not_mem
    {κ : Type*} [Field κ] {E : Type*} [Field E] [Algebra κ E]
    (Mb : Subalgebra κ E) (x : E) (hx : x ∈ Mb) (hxt : Transcendental κ x)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → E) (hb : ∀ i, b i ∈ Mb) (hfg : Mb.FG)
    (hspan : ∀ m ∈ Mb, ∃ q : ι → Polynomial κ, m = ∑ i, Polynomial.aeval x (q i) * b i)
    (hli : LinearIndependent (IntermediateField.adjoin κ ({x} : Set E)) b)
    (htop : Submodule.span (IntermediateField.adjoin κ ({x} : Set E)) (Set.range b) = ⊤)
    (Δ : E) (hΔ : Δ = (Algebra.discr (IntermediateField.adjoin κ ({x} : Set E)) b : E))
    (hΔM : Δ ∈ Mb)
    (𝔪 : Ideal Mb) [𝔪.IsMaximal] (h𝔪 : (⟨Δ, hΔM⟩ : Mb) ∉ 𝔪) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)).IsPrincipal := by
  classical

  haveI hpir : IsPrincipalIdealRing (Algebra.adjoin κ ({x} : Set E)) := redint_isPrincipalIdealRing_adjoin x
  have hR₀Mb : Algebra.adjoin κ ({x} : Set E) ≤ Mb := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx)
  have haev : ∀ q : κ[X], aeval x q ∈ Algebra.adjoin κ ({x} : Set E) := by
    intro q
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, rfl⟩
  haveI hKE : FiniteDimensional (IntermediateField.adjoin κ ({x} : Set E)) E :=
    Module.Finite.of_basis (Module.Basis.mk hli htop.ge)

  let f₀ : Algebra.adjoin κ ({x} : Set E) →ₐ[κ] Mb := Subalgebra.inclusion hR₀Mb
  let 𝔭 : Ideal (Algebra.adjoin κ ({x} : Set E)) := 𝔪.comap f₀
  haveI h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime f₀ 𝔪
  have hf₀coe : ∀ r : Algebra.adjoin κ ({x} : Set E), ((f₀ r : Mb) : E) = (r : E) := fun r => rfl
  have hρ₀ : ∀ r : Algebra.adjoin κ ({x} : Set E),
      algebraMap (Algebra.adjoin κ ({x} : Set E)) E r = (r : E) := fun r => rfl

  have hM₀ : ∀ m ∈ Mb, m ∈ Submodule.span (Algebra.adjoin κ ({x} : Set E)) (Set.range b) := by
    intro m hm
    obtain ⟨q, hq⟩ := hspan m hm
    rw [hq]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : (⟨aeval x (q i), haev (q i)⟩ : Algebra.adjoin κ ({x} : Set E)) • b i
        = aeval x (q i) * b i := by
      rw [Algebra.smul_def, hρ₀]
    rw [← h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hM₀one : (1 : E) ∈ Submodule.span (Algebra.adjoin κ ({x} : Set E)) (Set.range b) :=
    hM₀ 1 Mb.one_mem
  have hM₀prod : ∀ i j, b i * b j ∈ Submodule.span (Algebra.adjoin κ ({x} : Set E)) (Set.range b) :=
    fun i j => hM₀ _ (Mb.mul_mem (hb i) (hb j))
  have hMbint₀ : ∀ n : Mb, IsIntegral (Algebra.adjoin κ ({x} : Set E)) (n : E) := fun n =>
    redint_isIntegral_of_mem_span b hM₀one hM₀prod (hM₀ n n.2)
  have hM₀Mb : ∀ e ∈ Submodule.span (Algebra.adjoin κ ({x} : Set E)) (Set.range b), e ∈ Mb := by
    intro e he
    refine Submodule.span_induction ?_ ?_ ?_ ?_ he
    · rintro _ ⟨i, rfl⟩
      exact hb i
    · exact Mb.zero_mem
    · intro e₁ e₂ _ _ h₁ h₂
      exact Mb.add_mem h₁ h₂
    · intro r e₁ _ h₁
      rw [Algebra.smul_def, hρ₀]
      exact Mb.mul_mem (hR₀Mb r.2) h₁

  let R : Subalgebra (Algebra.adjoin κ ({x} : Set E)) (IntermediateField.adjoin κ ({x} : Set E)) :=
    Localization.subalgebra (IntermediateField.adjoin κ ({x} : Set E)) 𝔭.primeCompl
      𝔭.primeCompl_le_nonZeroDivisors
  haveI hRloc : IsLocalization 𝔭.primeCompl R :=
    Localization.subalgebra.isLocalization_subalgebra (IntermediateField.adjoin κ ({x} : Set E))
      𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
  haveI hRic : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
  have hρ : ∀ r : Algebra.adjoin κ ({x} : Set E),
      algebraMap R E (algebraMap (Algebra.adjoin κ ({x} : Set E)) R r) = (r : E) := fun r => rfl
  have hcoe : ∀ ρ : R, algebraMap R E ρ
      = ((algebraMap R (IntermediateField.adjoin κ ({x} : Set E)) ρ :
          IntermediateField.adjoin κ ({x} : Set E)) : E) :=
    fun ρ => rfl

  have hMbS : ∀ m ∈ Mb, m ∈ Submodule.span R (Set.range b) := by
    intro m hm
    obtain ⟨q, hq⟩ := hspan m hm
    rw [hq]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : (algebraMap (Algebra.adjoin κ ({x} : Set E)) R ⟨aeval x (q i), haev (q i)⟩) • b i
        = aeval x (q i) * b i := by
      rw [Algebra.smul_def, hρ]
    rw [← h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hSone : (1 : E) ∈ Submodule.span R (Set.range b) := hMbS 1 Mb.one_mem
  have hSprod : ∀ i j, b i * b j ∈ Submodule.span R (Set.range b) :=
    fun i j => hMbS _ (Mb.mul_mem (hb i) (hb j))

  have hd : ∃ d : R, IsUnit d ∧
      algebraMap R (IntermediateField.adjoin κ ({x} : Set E)) d
        = Algebra.discr (IntermediateField.adjoin κ ({x} : Set E)) b := by
    obtain ⟨D, hD⟩ := redint_exists_aeval_eq_discr x b fun i => hMbint₀ ⟨b i, hb i⟩
    let d₀ : Algebra.adjoin κ ({x} : Set E) := ⟨aeval x D, haev D⟩
    have hd₀ : f₀ d₀ = ⟨Δ, hΔM⟩ := by
      apply Subtype.ext
      rw [hf₀coe]
      change aeval x D = Δ
      rw [hΔ, hD]
    refine ⟨algebraMap (Algebra.adjoin κ ({x} : Set E)) R d₀, ?_, ?_⟩
    · refine (IsLocalization.AtPrime.isUnit_to_map_iff R 𝔭 d₀).mpr ?_
      intro hmem
      apply h𝔪
      rw [← hd₀]
      exact Ideal.mem_comap.mp hmem
    · apply Subtype.ext
      rw [← hcoe, hρ]
      change aeval x D = _
      exact hD.symm
  have hintR : ∀ e : E, IsIntegral R e → e ∈ Submodule.span R (Set.range b) :=
    redint_mem_span_of_isIntegral b hSone hSprod hli htop hd
  have hMbR : ∀ n : Mb, IsIntegral R (n : E) := fun n =>
    redint_isIntegral_of_mem_span b hSone hSprod (hMbS n n.2)

  haveI : IsDomain (Localization.AtPrime 𝔪) :=
    IsLocalization.isDomain_of_local_atPrime (Ideal.IsMaximal.isPrime ‹𝔪.IsMaximal›)
  haveI : Algebra.FiniteType κ Mb := (Subalgebra.fg_iff_finiteType Mb).mp hfg
  haveI : IsNoetherianRing Mb := Algebra.FiniteType.isNoetherianRing κ Mb
  have h34 : (IsIntegrallyClosed (Localization.AtPrime 𝔪) ∧
      ∀ P : Ideal (Localization.AtPrime 𝔪), P ≠ ⊥ → P.IsPrime →
        P = IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) ↔
      (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)).IsPrincipal :=
    (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime 𝔪)).out 3 4
  refine h34.mp ⟨?_, ?_⟩
  ·
    refine redint_isIntegrallyClosed_atPrime Mb 𝔪 ?_ ?_
    · intro z
      have hsp : ∀ u : E, ∃ c : ι → IntermediateField.adjoin κ ({x} : Set E),
          u = ∑ i, (c i : E) * b i := by
        intro u
        have hu : u ∈ Submodule.span (IntermediateField.adjoin κ ({x} : Set E)) (Set.range b) := by
          rw [htop]; exact Submodule.mem_top
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hu
        refine ⟨c, ?_⟩
        rw [← hc]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [IntermediateField.smul_def, smul_eq_mul]
      exact redint_exists_mul_mem Mb x hx hxt b hb hsp z
    · intro w hw
      have hwR : IsIntegral R w := redint_isIntegral_of_isIntegral_subalgebra Mb hMbR hw
      obtain ⟨u, hu⟩ := redint_exists_mul_mem_span 𝔭 (Rₚ := R) (fun a => hρ a) b (hintR w hwR)
      have hu𝔪 : f₀ u ∈ 𝔪.primeCompl := fun h => u.2 (Ideal.mem_comap.mpr h)
      refine ⟨⟨_, hM₀Mb _ hu⟩, ⟨f₀ u, hu𝔪⟩, ?_⟩
      change w * ((f₀ u : Mb) : E) = algebraMap (Algebra.adjoin κ ({x} : Set E)) E u * w
      rw [hf₀coe, hρ₀, mul_comm]
  ·
    intro P hP0 hP
    have hint₀ : ∀ n : Mb, (f₀ : Algebra.adjoin κ ({x} : Set E) →+* Mb).IsIntegralElem n := by
      intro n
      obtain ⟨p, hpm, hp⟩ := hMbint₀ n
      refine ⟨p, hpm, ?_⟩
      apply Subtype.val_injective
      have h := Polynomial.hom_eval₂ p (f₀ : Algebra.adjoin κ ({x} : Set E) →+* Mb)
        (Mb.val : Mb →+* E) n
      have hcomp : (Mb.val : Mb →+* E).comp (f₀ : Algebra.adjoin κ ({x} : Set E) →+* Mb)
          = algebraMap (Algebra.adjoin κ ({x} : Set E)) E := RingHom.ext fun r => rfl
      rw [hcomp] at h
      exact h.trans hp
    letI alg₀ : Algebra (Algebra.adjoin κ ({x} : Set E)) Mb :=
      (f₀ : Algebra.adjoin κ ({x} : Set E) →+* Mb).toAlgebra
    haveI : Algebra.IsIntegral (Algebra.adjoin κ ({x} : Set E)) Mb := ⟨hint₀⟩
    exact redint_prime_eq_maximalIdeal (A := Algebra.adjoin κ ({x} : Set E)) 𝔪 P hP0 hP

end Seven

section PlaneData

open Polynomial

section Places

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

private theorem plane_ord_algebraMap (v : AlgebraicCurve.Place L F) (a : L) :
    v.ord (algebraMap L F a) = 0 := by
  by_cases ha : a = 0
  · rw [ha, map_zero, AlgebraicCurve.Place.ord_zero]
  · have hu : IsUnit (⟨algebraMap L F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) := by
      refine ⟨⟨⟨algebraMap L F a, v.algebraMap_mem' a⟩, ⟨algebraMap L F a⁻¹, v.algebraMap_mem' a⁻¹⟩,
        ?_, ?_⟩, rfl⟩
      · ext; simp [ha]
      · ext; simp [ha]
    have := v.ord_coe_unit hu.unit
    simpa using this

private theorem plane_mem_maximalIdeal_of_ord_pos (v : AlgebraicCurve.Place L F) {g : F}
    (hg : g ∈ v.toValuationSubring) (h : 0 < v.ord g) :
    (⟨g, hg⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  by_contra hn
  have hu : IsUnit (⟨g, hg⟩ : v.toValuationSubring) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hn
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  rw [this] at h
  exact lt_irrefl 0 h

private theorem plane_ord_pos_of_mem_maximalIdeal (v : AlgebraicCurve.Place L F) {g : F}
    (hg : g ∈ v.toValuationSubring) (hg0 : g ≠ 0)
    (hm : (⟨g, hg⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    0 < v.ord g := by
  have h0 : 0 ≤ v.ord g := (redint_mem_iff_ord_nonneg v g).mp hg
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨w, hw⟩ := v.exists_unit_mul_zpow hg0 hπ
    rw [← h, zpow_zero, mul_one] at hw
    have : (⟨g, hg⟩ : v.toValuationSubring) = (w : v.toValuationSubring) := Subtype.ext hw
    rw [this] at hm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm w.isUnit

private theorem plane_evalAt_eq_zero (v : AlgebraicCurve.Place L F) {g : F}
    (hg : g ∈ v.toValuationSubring) (h : 0 < v.ord g) : v.evalAt g = 0 := by
  rw [v.evalAt_of_mem hg, (IsLocalRing.residue_eq_zero_iff _).mpr
    (plane_mem_maximalIdeal_of_ord_pos v hg h), ← map_zero (algebraMap L v.ResidueField),
    v.residueInv_algebraMap]

private theorem plane_ord_sub_evalAt_pos (v : AlgebraicCurve.Place L F) (hv : v.IsRational)
    {g : F} (hg : g ∈ v.toValuationSubring) (hne : g - algebraMap L F (v.evalAt g) ≠ 0) :
    0 < v.ord (g - algebraMap L F (v.evalAt g)) := by
  have hmem : g - algebraMap L F (v.evalAt g) ∈ v.toValuationSubring :=
    sub_mem hg (v.algebraMap_mem' _)
  refine plane_ord_pos_of_mem_maximalIdeal v hmem hne ?_
  rw [← IsLocalRing.residue_eq_zero_iff]
  have h1 := v.algebraMap_evalAt hv hg
  have h2 : (⟨g - algebraMap L F (v.evalAt g), hmem⟩ : v.toValuationSubring)
      = ⟨g, hg⟩ - algebraMap L v.toValuationSubring (v.evalAt g) := by
    ext; simp
  rw [h2, map_sub, ← h1]
  exact sub_eq_zero.mpr rfl

private theorem plane_evalAt_eq_of_ord_sub_pos (v : AlgebraicCurve.Place L F) (hv : v.IsRational)
    {g : F} (hg : g ∈ v.toValuationSubring) {a : L}
    (h : 0 < v.ord (g - algebraMap L F a)) : v.evalAt g = a := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hg]
  have hmem : g - algebraMap L F a ∈ v.toValuationSubring := sub_mem hg (v.algebraMap_mem' _)
  have h1 : IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap L F a, hmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (plane_mem_maximalIdeal_of_ord_pos v hmem h)
  have h2 : (⟨g, hg⟩ : v.toValuationSubring)
      = ⟨g - algebraMap L F a, hmem⟩ + algebraMap L v.toValuationSubring a := by
    ext; simp
  rw [h2, map_add, h1, zero_add]
  rfl

private theorem plane_isRational [IsAlgClosed L] (f : F) (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (v : AlgebraicCurve.Place L F) : v.IsRational := by
  haveI : AlgebraicCurve.IsCurveOver L F :=
    AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental f hf
  have hdeg : Module.finrank L v.ResidueField = 1 :=
    AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed v
  exact ((Algebra.finrank_eq_one_iff_bijective_algebraMap).mp hdeg).2

private theorem plane_transcendental_of_ord_ne_zero [IsAlgClosed L] (v : AlgebraicCurve.Place L F)
    {t : F} (ht : v.ord t ≠ 0) : Transcendental L t := by
  intro halg
  have hdeg : (minpoly L t).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible halg.isIntegral)
  obtain ⟨a, ha⟩ := minpoly.mem_range_of_degree_eq_one L t hdeg
  rw [← ha] at ht
  exact ht (plane_ord_algebraMap v a)

private theorem plane_aeval_mem (f : F) (p : L[X]) (V : ValuationSubring F)
    (hL : ∀ c : L, algebraMap L F c ∈ V) (hf : f ∈ V) : aeval f p ∈ V := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n c =>
    rw [aeval_monomial]
    exact mul_mem (hL c) (pow_mem hf n)

private theorem plane_mem_of_isIntegral (f : F) (V : ValuationSubring F)
    (hL : ∀ c : L, algebraMap L F c ∈ V) (hf : f ∈ V) {x : F}
    (hx : IsIntegral (Algebra.adjoin L ({f} : Set F)) x) : x ∈ V := by
  have hle : ∀ y : Algebra.adjoin L ({f} : Set F), (y : F) ∈ V := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    exact plane_aeval_mem f p V hL hf
  set φ : Algebra.adjoin L ({f} : Set F) →+* V :=
    (algebraMap (Algebra.adjoin L ({f} : Set F)) F).codRestrict V hle with hφ
  obtain ⟨p, hpm, hpx⟩ := hx
  have hint : IsIntegral V x := by
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [eval₂_map]
    exact hpx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← hy]
  exact y.2

end Places

section Uniformizer

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

open scoped IntermediateField.algebraAdjoinAdjoin in

private theorem plane_exists_integral_primitive (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F] :
    ∃ θ : F, IsIntegral (Algebra.adjoin L ({f} : Set F)) θ ∧
      IntermediateField.adjoin L ({f, θ} : Set F) = ⊤ := by
  obtain ⟨θ₀, hθ₀⟩ := Field.exists_primitive_element (IntermediateField.adjoin L ({f} : Set F)) F
  have halg : IsAlgebraic (Algebra.adjoin L ({f} : Set F)) θ₀ :=
    (IsFractionRing.isAlgebraic_iff (Algebra.adjoin L ({f} : Set F))
      (IntermediateField.adjoin L ({f} : Set F)) F).mpr (Algebra.IsAlgebraic.isAlgebraic θ₀)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  have hy0' : (y : F) ≠ 0 := fun h => hy0 (Subtype.ext h)
  refine ⟨(y : F) * θ₀, ?_, ?_⟩
  · rw [Algebra.smul_def] at hyint
    exact hyint
  · have h1 : IntermediateField.adjoin L ({f, θ₀} : Set F) = ⊤ := by
      rw [← IntermediateField.adjoin_simple_adjoin_simple, hθ₀,
        IntermediateField.restrictScalars_top]
    have hfK : f ∈ IntermediateField.adjoin L ({f, (y : F) * θ₀} : Set F) :=
      IntermediateField.subset_adjoin L _ (Set.mem_insert _ _)
    have hyθK : (y : F) * θ₀ ∈ IntermediateField.adjoin L ({f, (y : F) * θ₀} : Set F) :=
      IntermediateField.subset_adjoin L _ (Set.mem_insert_of_mem _ rfl)
    have hyK : (y : F) ∈ IntermediateField.adjoin L ({f, (y : F) * θ₀} : Set F) := by
      have hle : Algebra.adjoin L ({f} : Set F)
          ≤ (IntermediateField.adjoin L ({f, (y : F) * θ₀} : Set F)).toSubalgebra :=
        Algebra.adjoin_le (Set.singleton_subset_iff.mpr hfK)
      exact hle y.2
    rw [eq_top_iff, ← h1, IntermediateField.adjoin_le_iff]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact hfK
    · rw [Set.mem_singleton_iff.mp hx]
      have := mul_mem (inv_mem hyK) hyθK
      rwa [inv_mul_cancel_left₀ hy0'] at this

private theorem plane_exists_gen [Infinite L] (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z₀ m θ : F) (hm : m ∈ IntermediateField.adjoin L ({f} : Set F)) (hm0 : m ≠ 0)
    (hθ : IntermediateField.adjoin L ({f, θ} : Set F) = ⊤) :
    ∃ a : L, IntermediateField.adjoin L ({f, z₀ + algebraMap L F a * (m * θ)} : Set F) = ⊤ := by
  have hprim : IntermediateField.adjoin (IntermediateField.adjoin L ({f} : Set F)) ({θ} : Set F)
      = ⊤ := by
    apply IntermediateField.restrictScalars_injective L
    rw [IntermediateField.restrictScalars_top, IntermediateField.adjoin_simple_adjoin_simple, hθ]
  haveI : Finite (IntermediateField (IntermediateField.adjoin L ({f} : Set F)) F) :=
    Field.finite_intermediateField_of_exists_primitive_element _ F ⟨θ, hprim⟩
  obtain ⟨a₁, a₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun a : L => IntermediateField.adjoin (IntermediateField.adjoin L ({f} : Set F))
      ({z₀ + algebraMap L F a * (m * θ)} : Set F))
  refine ⟨a₁, ?_⟩
  set K' := IntermediateField.adjoin (IntermediateField.adjoin L ({f} : Set F))
      ({z₀ + algebraMap L F a₁ * (m * θ)} : Set F) with hK'
  have h1 : z₀ + algebraMap L F a₁ * (m * θ) ∈ K' :=
    IntermediateField.mem_adjoin_simple_self _ _
  have heq' : IntermediateField.adjoin (IntermediateField.adjoin L ({f} : Set F))
        ({z₀ + algebraMap L F a₁ * (m * θ)} : Set F)
      = IntermediateField.adjoin (IntermediateField.adjoin L ({f} : Set F))
        ({z₀ + algebraMap L F a₂ * (m * θ)} : Set F) := heq
  have h2 : z₀ + algebraMap L F a₂ * (m * θ) ∈ K' := by
    have := IntermediateField.mem_adjoin_simple_self (IntermediateField.adjoin L ({f} : Set F))
      (z₀ + algebraMap L F a₂ * (m * θ))
    rwa [← heq'] at this
  have hconst : ∀ b : L, algebraMap L F b ∈ K' := by
    intro b
    have := K'.algebraMap_mem (algebraMap L (IntermediateField.adjoin L ({f} : Set F)) b)
    rwa [← IsScalarTower.algebraMap_apply] at this
  have hmK : m ∈ K' := K'.algebraMap_mem ⟨m, hm⟩
  have hθK : θ ∈ K' := by
    have hd : algebraMap L F (a₁ - a₂) * (m * θ) ∈ K' := by
      have := sub_mem h1 h2
      convert this using 1
      rw [map_sub]; ring
    have ha : algebraMap L F (a₁ - a₂) ≠ 0 := by
      rw [_root_.map_ne_zero]; exact sub_ne_zero.mpr hne
    have hmθ : m * θ ∈ K' := by
      have := mul_mem (inv_mem (hconst (a₁ - a₂))) hd
      rwa [inv_mul_cancel_left₀ ha] at this
    have := mul_mem (inv_mem hmK) hmθ
    rwa [inv_mul_cancel_left₀ hm0] at this
  have htop : K' = ⊤ := by
    rw [eq_top_iff, ← hprim, IntermediateField.adjoin_le_iff]
    exact Set.singleton_subset_iff.mpr hθK
  have := congrArg (IntermediateField.restrictScalars L) htop
  rw [IntermediateField.restrictScalars_top, hK',
    IntermediateField.adjoin_simple_adjoin_simple] at this
  exact this

private theorem plane_exists_pole_forcing [IsAlgClosed L] (f : F) (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (c : L) (z₁ : F) (hz₁ : z₁ ≠ 0) :
    ∃ N : ℕ, ∀ P : AlgebraicCurve.Place L F, P.ord f < 0 →
      P.ord (z₁ * (f - algebraMap L F c + 1) ^ N) < 0 := by
  classical
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)
  have hg : f - algebraMap L F c + 1 = f + algebraMap L F (1 - c) := by
    rw [map_sub, map_one]; ring
  have hg0 : f - algebraMap L F c + 1 ≠ 0 := by
    intro h
    apply hf
    have : f = algebraMap L F (c - 1) := by
      rw [map_sub, map_one]; linear_combination h
    rw [this]; exact isAlgebraic_algebraMap _
  have hfin := redint_finite_zeros f hf f⁻¹ (inv_ne_zero hf0)
  refine ⟨(hfin.toFinset.sup fun P => (P.ord z₁).toNat) + 1, fun P hP => ?_⟩
  have hPmem : P ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show 0 < P.ord f⁻¹
    rw [P.ord_inv]; omega
  have hle : (P.ord z₁).toNat ≤ hfin.toFinset.sup fun P => (P.ord z₁).toNat :=
    Finset.le_sup (f := fun P => (P.ord z₁).toNat) hPmem
  have hordg : P.ord (f - algebraMap L F c + 1) = P.ord f := by
    rw [hg]
    by_cases hc : (1 - c) = 0
    · rw [hc, map_zero, add_zero]
    · have hc' : algebraMap L F (1 - c) ≠ 0 := by rwa [_root_.map_ne_zero]
      exact P.ord_add_eq_of_lt hf0 hc' (by rw [plane_ord_algebraMap]; exact hP)
  rw [P.ord_mul hz₁ (pow_ne_zero _ hg0), ← zpow_natCast, P.ord_zpow, hordg]
  set S := hfin.toFinset.sup fun P => (P.ord z₁).toNat with hS
  have h1 : ((S + 1 : ℕ) : ℤ) * P.ord f ≤ ((S + 1 : ℕ) : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have h2 : P.ord z₁ ≤ ((P.ord z₁).toNat : ℤ) := Int.self_le_toNat _
  have h3 : ((P.ord z₁).toNat : ℤ) ≤ (S : ℤ) := by exact_mod_cast hle
  push_cast at h1 ⊢
  linarith

end Uniformizer

section Relation

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

private theorem plane_exists_monic_relation {z : F} (hz : Transcendental L z) {f : F}
    (hfz : IsIntegral (Algebra.adjoin L ({z} : Set F)) f) :
    ∃ H : Polynomial (Polynomial L), H.Monic ∧
      (H.map (mapRingHom (algebraMap L F))).evalEval z f = 0 := by
  have hinj : Function.Injective (aeval z : L[X] →ₐ[L] F) := transcendental_iff_injective.mp hz
  set e : L[X] ≃ₐ[L] Algebra.adjoin L ({z} : Set F) :=
    (AlgEquiv.ofInjective (aeval z : L[X] →ₐ[L] F) hinj).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval L z).symm) with hedef
  have he : ∀ q : L[X], ((e q : Algebra.adjoin L ({z} : Set F)) : F) = aeval z q := fun q => rfl
  set es : Algebra.adjoin L ({z} : Set F) →+* L[X] := e.symm.toRingEquiv.toRingHom with hesdef
  have hes : ∀ a, es a = e.symm a := fun a => rfl
  obtain ⟨p, hpm, hpf⟩ := hfz
  refine ⟨p.map es, hpm.map es, ?_⟩
  have hψ : (evalRingHom z).comp ((mapRingHom (algebraMap L F)).comp es)
      = algebraMap (Algebra.adjoin L ({z} : Set F)) F := by
    ext a
    simp only [RingHom.comp_apply, coe_evalRingHom, coe_mapRingHom, eval_map, hes]
    rw [← aeval_def, ← he (e.symm a), AlgEquiv.apply_symm_apply]
    rfl
  rw [Polynomial.map_map]
  show ((p.map ((mapRingHom (algebraMap L F)).comp es)).eval (C f)).eval z = 0
  rw [eval_map, ← coe_evalRingHom, hom_eval₂, hψ, coe_evalRingHom, eval_C]
  exact hpf

private theorem plane_exists_irreducible_factor {H : Polynomial (Polynomial L)} (hH : H.Monic)
    {z f : F} (hHz : (H.map (mapRingHom (algebraMap L F))).evalEval z f = 0) :
    ∃ G : Polynomial (Polynomial L), Irreducible G ∧
      (G.map (mapRingHom (algebraMap L F))).evalEval z f = 0 ∧
      ∃ r : L, r ≠ 0 ∧ G.leadingCoeff = C r := by
  classical
  set Ψ : Polynomial (Polynomial L) →+* F :=
    (evalEvalRingHom z f).comp (mapRingHom (mapRingHom (algebraMap L F))) with hΨdef
  have hΨ : ∀ q, Ψ q = (q.map (mapRingHom (algebraMap L F))).evalEval z f := fun q => rfl
  have hH0 : H ≠ 0 := hH.ne_zero
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hH0
  have h1 : Ψ (UniqueFactorizationMonoid.factors H).prod * Ψ ↑u = 0 := by
    rw [← map_mul, hu, hΨ, hHz]
  have hu0 : Ψ ↑u ≠ 0 := (u.isUnit.map Ψ).ne_zero
  have h2 : ((UniqueFactorizationMonoid.factors H).map Ψ).prod = 0 := by
    rw [← map_multiset_prod]
    exact (mul_eq_zero.mp h1).resolve_right hu0
  obtain ⟨G, hGmem, hG0⟩ : ∃ G ∈ UniqueFactorizationMonoid.factors H, Ψ G = 0 := by
    simpa using Multiset.prod_eq_zero_iff.mp h2
  refine ⟨G, UniqueFactorizationMonoid.irreducible_of_factor G hGmem, (hΨ G) ▸ hG0, ?_⟩
  have hdvd : G ∣ H := (Multiset.dvd_prod hGmem).trans ⟨↑u, hu.symm⟩
  have hlc : G.leadingCoeff ∣ H.leadingCoeff := leadingCoeff_dvd_leadingCoeff hdvd
  rw [hH.leadingCoeff] at hlc
  obtain ⟨r, hr, hrC⟩ := Polynomial.isUnit_iff.mp (isUnit_of_dvd_one hlc)
  exact ⟨r, hr.ne_zero, hrC.symm⟩

private theorem plane_evalEval_eq_zero (Q : AlgebraicCurve.Place L F) {z f : F} (c : L)
    (hz : z ∈ Q.toValuationSubring) (hf : f ∈ Q.toValuationSubring)
    (hz1 : 0 < Q.ord z) (hfc : 0 < Q.ord (f - algebraMap L F c))
    (G : Polynomial (Polynomial L))
    (hG : (G.map (mapRingHom (algebraMap L F))).evalEval z f = 0) :
    G.evalEval 0 c = 0 := by
  have hcomp : Q.toValuationSubring.subtype.comp (algebraMap L Q.toValuationSubring)
      = algebraMap L F := RingHom.ext fun a => rfl
  have hmap : (G.map (mapRingHom (algebraMap L Q.toValuationSubring))).map
      (mapRingHom Q.toValuationSubring.subtype) = G.map (mapRingHom (algebraMap L F)) := by
    rw [Polynomial.map_map]
    congr 1
    refine RingHom.ext fun q => ?_
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_map, hcomp]
  set E := (G.map (mapRingHom (algebraMap L Q.toValuationSubring))).evalEval ⟨z, hz⟩ ⟨f, hf⟩
    with hEdef
  have key : Q.toValuationSubring.subtype E = 0 := by
    rw [hEdef, ← map_mapRingHom_evalEval Q.toValuationSubring.subtype, hmap]
    exact hG
  have hE0 : E = 0 := (map_eq_zero_iff _ Subtype.val_injective).mp key
  have hres := congrArg (IsLocalRing.residue Q.toValuationSubring) hE0
  rw [map_zero, hEdef, ← map_mapRingHom_evalEval (IsLocalRing.residue Q.toValuationSubring),
    Polynomial.map_map] at hres
  have hz0 : IsLocalRing.residue Q.toValuationSubring ⟨z, hz⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (plane_mem_maximalIdeal_of_ord_pos Q hz hz1)
  have hfcmem : f - algebraMap L F c ∈ Q.toValuationSubring := sub_mem hf (Q.algebraMap_mem' c)
  have hf0 : IsLocalRing.residue Q.toValuationSubring ⟨f, hf⟩
      = algebraMap L Q.ResidueField c := by
    have h1 : IsLocalRing.residue Q.toValuationSubring ⟨f - algebraMap L F c, hfcmem⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr (plane_mem_maximalIdeal_of_ord_pos Q hfcmem hfc)
    have h2 : (⟨f, hf⟩ : Q.toValuationSubring)
        = ⟨f - algebraMap L F c, hfcmem⟩ + algebraMap L Q.toValuationSubring c := by
      ext; simp
    rw [h2, map_add, h1, zero_add]
    rfl
  rw [hz0, hf0] at hres
  have hcomp2 : (IsLocalRing.residue Q.toValuationSubring).comp
      (algebraMap L Q.toValuationSubring) = algebraMap L Q.ResidueField :=
    RingHom.ext fun a => rfl
  have hmap2 : G.map ((mapRingHom (IsLocalRing.residue Q.toValuationSubring)).comp
      (mapRingHom (algebraMap L Q.toValuationSubring)))
      = G.map (mapRingHom (algebraMap L Q.ResidueField)) := by
    congr 1
    refine RingHom.ext fun q => ?_
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_map, hcomp2]
  rw [hmap2] at hres
  have h3 : (G.map (mapRingHom (algebraMap L Q.ResidueField))).evalEval
      (algebraMap L Q.ResidueField 0) (algebraMap L Q.ResidueField c) = 0 := by
    rwa [map_zero]
  rw [map_mapRingHom_evalEval] at h3
  exact (map_eq_zero_iff _ (algebraMap L Q.ResidueField).injective).mp h3

end Relation

private theorem redint_exists_plane_data
    {L : Type u} [Field L] [IsAlgClosed L] {F : Type v} [Field F] [Algebra L F] (f : F)
    (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    (c : L) (Q : AlgebraicCurve.Place L F) (hQ : 0 < Q.ord (f - algebraMap L F c)) :
    ∃ (z : F) (G : Polynomial (Polynomial L)),
      (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → z ∈ V) ∧
      Q.ord z = 1 ∧
      (∀ Q' : AlgebraicCurve.Place L F, Q' ≠ Q → 0 < Q'.ord (f - algebraMap L F c) → Q'.ord z = 0) ∧
      IntermediateField.adjoin L ({f, z} : Set F) = ⊤ ∧
      (G.map (Polynomial.mapRingHom (algebraMap L F))).evalEval z f = 0 ∧
      G.evalEval 0 c = 0 ∧
      (Polynomial.derivative G).evalEval 0 c ≠ 0 := by
  classical
  have hfc0 : f - algebraMap L F c ≠ 0 := by
    intro h
    apply hf
    rw [sub_eq_zero.mp h]
    exact isAlgebraic_algebraMap c

  have hTfin := redint_finite_zeros f hf (f - algebraMap L F c) hfc0
  set T := hTfin.toFinset with hTdef
  have hT : ∀ Q' : AlgebraicCurve.Place L F, Q' ∈ T ↔ 0 < Q'.ord (f - algebraMap L F c) :=
    fun Q' => Set.Finite.mem_toFinset _
  have hQT : Q ∈ T := (hT Q).mpr hQ
  have hfT : ∀ Q' ∈ T, f ∈ Q'.toValuationSubring := by
    intro Q' hQ'
    have h1 : f - algebraMap L F c ∈ Q'.toValuationSubring :=
      (redint_mem_iff_ord_nonneg Q' _).mpr ((hT Q').mp hQ').le
    have h2 := add_mem h1 (Q'.algebraMap_mem' c)
    rwa [sub_add_cancel] at h2

  obtain ⟨z₀, hz₀int, hz₀Q, hz₀T⟩ :=
    AlgebraicCurve.Place.exists_isIntegral_adjoin_and_ord_eq_one_and_forall_ord_eq_zero
      f hf T Q hQT hfT
  have hz₀0 : z₀ ≠ 0 := by
    intro h; rw [h, AlgebraicCurve.Place.ord_zero] at hz₀Q; exact zero_ne_one hz₀Q

  obtain ⟨θ, hθint, hθgen⟩ := plane_exists_integral_primitive (L := L) f
  have hm : (f - algebraMap L F c) ^ 2 ∈ IntermediateField.adjoin L ({f} : Set F) :=
    pow_mem (sub_mem (IntermediateField.mem_adjoin_simple_self L f)
      ((IntermediateField.adjoin L ({f} : Set F)).algebraMap_mem c)) 2
  obtain ⟨a, ha⟩ := plane_exists_gen f z₀ ((f - algebraMap L F c) ^ 2) θ hm (pow_ne_zero 2 hfc0) hθgen
  set z₁ := z₀ + algebraMap L F a * ((f - algebraMap L F c) ^ 2 * θ) with hz₁def
  have hz₁V : ∀ V : ValuationSubring F, (∀ b : L, algebraMap L F b ∈ V) → f ∈ V → z₁ ∈ V := by
    intro V hV hfV
    have h0 := plane_mem_of_isIntegral f V hV hfV hz₀int
    have h1 := plane_mem_of_isIntegral f V hV hfV hθint
    exact add_mem h0 (mul_mem (hV a) (mul_mem (pow_mem (sub_mem hfV (hV c)) 2) h1))
  have hpert : ∀ Q' ∈ T, Q'.ord z₁ = Q'.ord z₀ := by
    intro Q' hQ'
    by_cases hu : algebraMap L F a * ((f - algebraMap L F c) ^ 2 * θ) = 0
    · rw [hz₁def, hu, add_zero]
    · have ha0 : algebraMap L F a ≠ 0 := left_ne_zero_of_mul hu
      have hmθ : (f - algebraMap L F c) ^ 2 * θ ≠ 0 := right_ne_zero_of_mul hu
      have hθ0 : θ ≠ 0 := right_ne_zero_of_mul hmθ
      have hm0 : (f - algebraMap L F c) ^ 2 ≠ 0 := left_ne_zero_of_mul hmθ
      have hθord : 0 ≤ Q'.ord θ := (redint_mem_iff_ord_nonneg Q' θ).mp
        (plane_mem_of_isIntegral f _ Q'.algebraMap_mem' (hfT Q' hQ') hθint)
      have hmord : Q'.ord ((f - algebraMap L F c) ^ 2) = 2 * Q'.ord (f - algebraMap L F c) := by
        rw [← zpow_natCast, Q'.ord_zpow]; norm_cast
      have hpos := (hT Q').mp hQ'
      have hordu : 2 ≤ Q'.ord (algebraMap L F a * ((f - algebraMap L F c) ^ 2 * θ)) := by
        rw [Q'.ord_mul ha0 hmθ, Q'.ord_mul hm0 hθ0, plane_ord_algebraMap, zero_add, hmord]
        omega
      have hz₀le : Q'.ord z₀ ≤ 1 := by
        by_cases hQQ : Q' = Q
        · rw [hQQ, hz₀Q]
        · rw [hz₀T Q' hQ' hQQ]; exact zero_le_one
      rw [hz₁def, Q'.ord_add_eq_of_lt hz₀0 hu (by omega)]
  have hz₁Q : Q.ord z₁ = 1 := (hpert Q hQT).trans hz₀Q
  have hz₁0 : z₁ ≠ 0 := by
    intro h; rw [h, AlgebraicCurve.Place.ord_zero] at hz₁Q; exact zero_ne_one hz₁Q

  obtain ⟨N, hN⟩ := plane_exists_pole_forcing f hf c z₁ hz₁0
  have hg0 : f - algebraMap L F c + 1 ≠ 0 := by
    intro h
    apply hf
    have : f = algebraMap L F (c - 1) := by
      rw [map_sub, map_one]; linear_combination h
    rw [this]; exact isAlgebraic_algebraMap _
  set g := f - algebraMap L F c + 1 with hgdef
  set z := z₁ * g ^ N with hzdef
  have hzV : ∀ V : ValuationSubring F, (∀ b : L, algebraMap L F b ∈ V) → f ∈ V → z ∈ V :=
    fun V hV hfV => mul_mem (hz₁V V hV hfV) (pow_mem (add_mem (sub_mem hfV (hV c)) (one_mem V)) N)
  have hordg : ∀ Q' ∈ T, Q'.ord g = 0 := by
    intro Q' hQ'
    have h := (hT Q').mp hQ'
    have : g = 1 + (f - algebraMap L F c) := by rw [hgdef]; ring
    rw [this, Q'.ord_add_eq_of_lt one_ne_zero hfc0 (by rw [Q'.ord_one]; exact h), Q'.ord_one]
  have hordz : ∀ Q' ∈ T, Q'.ord z = Q'.ord z₀ := by
    intro Q' hQ'
    rw [hzdef, Q'.ord_mul hz₁0 (pow_ne_zero N hg0), ← zpow_natCast, Q'.ord_zpow, hordg Q' hQ',
      mul_zero, add_zero, hpert Q' hQ']
  have hzQ : Q.ord z = 1 := (hordz Q hQT).trans hz₀Q
  have hz0 : z ≠ 0 := by
    intro h; rw [h, AlgebraicCurve.Place.ord_zero] at hzQ; exact zero_ne_one hzQ
  have hzT : ∀ Q' : AlgebraicCurve.Place L F, Q' ≠ Q → 0 < Q'.ord (f - algebraMap L F c) →
      Q'.ord z = 0 :=
    fun Q' hne hpos => (hordz Q' ((hT Q').mpr hpos)).trans (hz₀T Q' ((hT Q').mpr hpos) hne)

  have hgen : IntermediateField.adjoin L ({f, z} : Set F) = ⊤ := by
    have hfK : f ∈ IntermediateField.adjoin L ({f, z} : Set F) :=
      IntermediateField.subset_adjoin L _ (Set.mem_insert _ _)
    have hzK : z ∈ IntermediateField.adjoin L ({f, z} : Set F) :=
      IntermediateField.subset_adjoin L _ (Set.mem_insert_of_mem _ rfl)
    have hgK : g ∈ IntermediateField.adjoin L ({f, z} : Set F) :=
      add_mem (sub_mem hfK ((IntermediateField.adjoin L ({f, z} : Set F)).algebraMap_mem c))
        (one_mem _)
    have hz₁K : z₁ ∈ IntermediateField.adjoin L ({f, z} : Set F) := by
      have : z₁ = z * (g ^ N)⁻¹ := by rw [hzdef, mul_inv_cancel_right₀ (pow_ne_zero N hg0)]
      rw [this]
      exact mul_mem hzK (inv_mem (pow_mem hgK N))
    rw [eq_top_iff, ← ha, IntermediateField.adjoin_le_iff]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact hfK
    · rw [Set.mem_singleton_iff.mp hx]; exact hz₁K

  have hfz : ∀ v : AlgebraicCurve.Place L F, z ∈ v.toValuationSubring → f ∈ v.toValuationSubring := by
    intro v hzv
    by_contra hfv
    have hordf : v.ord f < 0 := by
      have := (redint_mem_iff_ord_nonneg v f).not.mp hfv
      omega
    have h1 := hN v hordf
    have h2 := (redint_mem_iff_ord_nonneg v z).mp hzv
    omega
  have hfint : IsIntegral (Algebra.adjoin L ({z} : Set F)) f :=
    AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring f z f hfz
  have hzt : Transcendental L z := plane_transcendental_of_ord_ne_zero Q (by rw [hzQ]; exact one_ne_zero)

  obtain ⟨H, hHm, hHz⟩ := plane_exists_monic_relation hzt hfint
  obtain ⟨G, hGirr, hGz, r, hr0, hGlc⟩ := plane_exists_irreducible_factor hHm hHz

  have hrat : ∀ w : AlgebraicCurve.Place L F, w.IsRational := plane_isRational f hf
  haveI : Algebra.IsSeparable (IntermediateField.adjoin L ({z} : Set F)) F :=
    AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one f Q hzQ
  have hzQmem : z ∈ Q.toValuationSubring :=
    (redint_mem_iff_ord_nonneg Q z).mpr (by rw [hzQ]; exact zero_le_one)
  have hfQmem : f ∈ Q.toValuationSubring := hfT Q hQT
  have hzpos : 0 < Q.ord z := by rw [hzQ]; exact zero_lt_one
  have hevz : Q.evalAt z = 0 := plane_evalAt_eq_zero Q hzQmem hzpos
  have hevf : Q.evalAt f = c := plane_evalAt_eq_of_ord_sub_pos Q (hrat Q) hfQmem hQ
  have he : Q.ord (z - algebraMap L F (Q.evalAt z)) = 1 := by
    rw [hevz, map_zero, sub_zero, hzQ]
  have hlead : G.leadingCoeff.eval (Q.evalAt z) ≠ 0 := by
    rw [hGlc, eval_C]; exact hr0
  have hsep : ∀ Q' : AlgebraicCurve.Place L F, Q' ≠ Q → z ∈ Q'.toValuationSubring →
      Q'.evalAt z = Q.evalAt z → f ∈ Q'.toValuationSubring → Q'.evalAt f ≠ Q.evalAt f := by
    intro Q' hne hzQ' hevz' hfQ' hevf'
    rw [hevz] at hevz'
    rw [hevf] at hevf'
    have h1 : 0 < Q'.ord (f - algebraMap L F c) := by
      have := plane_ord_sub_evalAt_pos Q' (hrat Q') hfQ' (by rw [hevf']; exact hfc0)
      rwa [hevf'] at this
    have h2 : Q'.ord z = 0 := hzT Q' hne h1
    have h3 := plane_ord_sub_evalAt_pos Q' (hrat Q') hzQ' (by rw [hevz', map_zero, sub_zero]; exact hz0)
    rw [hevz', map_zero, sub_zero, h2] at h3
    exact lt_irrefl 0 h3
  have hder :=
    AlgebraicCurve.Place.derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne_of_isSeparable
      f hrat hzt G hGirr hGz Q hzQmem hfQmem he hlead hsep
  rw [hevz, hevf] at hder
  have hG0 : G.evalEval 0 c = 0 := plane_evalEval_eq_zero Q c hzQmem hfQmem hzpos hQ G hGz
  exact ⟨z, G, hzV, hzQ, hzT, hgen, hGz, hG0, hder⟩

end PlaneData

private theorem redint_exists_pow_prod_eq_mul
    {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F] (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    (c : L) (T : Finset (AlgebraicCurve.Place L F))
    (hT : ∀ Q : AlgebraicCurve.Place L F, Q ∈ T ↔ 0 < Q.ord (f - algebraMap L F c))
    (hfc : f - algebraMap L F c ≠ 0)
    (z : AlgebraicCurve.Place L F → F)
    (hzint : ∀ Q ∈ T, ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → z Q ∈ V)
    (hzord : ∀ Q ∈ T, 0 < Q.ord (z Q)) :
    ∃ (N : ℕ) (h : F),
      (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → h ∈ V) ∧
      (∏ Q ∈ T, z Q) ^ N = (f - algebraMap L F c) * h := by
  classical

  have hz0 : ∀ Q ∈ T, z Q ≠ 0 := by
    intro Q hQ h0
    have := hzord Q hQ
    rw [h0] at this
    simp at this
  obtain ⟨P, hP⟩ : ∃ P : F, P = ∏ Q ∈ T, z Q := ⟨_, rfl⟩
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact Finset.prod_ne_zero_iff.mpr hz0

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ Q ∈ T, Q.ord (f - algebraMap L F c) ≤ (N : ℤ) :=
    ⟨T.sup fun Q => (Q.ord (f - algebraMap L F c)).toNat, fun Q hQ =>
      (Int.self_le_toNat _).trans
        (Nat.cast_le.mpr (Finset.le_sup (f := fun Q => (Q.ord (f - algebraMap L F c)).toNat) hQ))⟩
  have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg N

  have hplace : ∀ v : AlgebraicCurve.Place L F, f ∈ v.toValuationSubring →
      P ^ N * (f - algebraMap L F c)⁻¹ ∈ v.toValuationSubring := by
    intro v hfv
    have hzv : ∀ Q ∈ T, z Q ∈ v.toValuationSubring :=
      fun Q hQ => hzint Q hQ v.toValuationSubring v.algebraMap_mem' hfv
    have hPmem : P ∈ v.toValuationSubring := by
      rw [hP]
      exact prod_mem hzv
    have hordP : 0 ≤ v.ord P := (redint_mem_iff_ord_nonneg v P).mp hPmem
    rw [redint_mem_iff_ord_nonneg, v.ord_mul (pow_ne_zero _ hP0) (inv_ne_zero hfc), ← zpow_natCast,
      v.ord_zpow, v.ord_inv]
    by_cases hvT : v ∈ T
    · have hrest : ∏ Q ∈ T.erase v, z Q ∈ v.toValuationSubring :=
        prod_mem fun Q hQ => hzv Q (Finset.mem_of_mem_erase hQ)
      have hrest0 : ∏ Q ∈ T.erase v, z Q ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun Q hQ => hz0 Q (Finset.mem_of_mem_erase hQ)
      have hsplit : P = z v * ∏ Q ∈ T.erase v, z Q := by
        rw [hP]
        exact (Finset.mul_prod_erase T z hvT).symm
      have hordP1 : 1 ≤ v.ord P := by
        have h1 := hzord v hvT
        have h2 := (redint_mem_iff_ord_nonneg v _).mp hrest
        rw [hsplit, v.ord_mul (hz0 v hvT) hrest0]
        omega
      have h3 := hN v hvT
      have h4 : (N : ℤ) * 1 ≤ (N : ℤ) * v.ord P := mul_le_mul_of_nonneg_left hordP1 hN0
      linarith
    · have h3 : v.ord (f - algebraMap L F c) ≤ 0 :=
        not_lt.mp fun hpos => hvT ((hT v).mpr hpos)
      have h4 : (0 : ℤ) ≤ (N : ℤ) * v.ord P := mul_nonneg hN0 hordP
      linarith
  refine ⟨N, P ^ N * (f - algebraMap L F c)⁻¹, ?_, ?_⟩
  · intro V hV hfV
    exact plane_mem_of_isIntegral f V hV hfV
      (AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring f f _ hplace)
  · rw [← hP, mul_left_comm, mul_inv_cancel₀ hfc, mul_one]

section CoordinateIdentity

open Polynomial

section Places

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

private theorem plane_residue_evalEval (Q : AlgebraicCurve.Place L F) {z f : F} (c : L)
    (hz : z ∈ Q.toValuationSubring) (hf : f ∈ Q.toValuationSubring)
    (hz1 : 0 < Q.ord z) (hfc : 0 < Q.ord (f - algebraMap L F c))
    (P : Polynomial (Polynomial L))
    (hP : (P.map (mapRingHom (algebraMap L F))).evalEval z f ∈ Q.toValuationSubring) :
    IsLocalRing.residue Q.toValuationSubring ⟨_, hP⟩
      = algebraMap L Q.ResidueField (P.evalEval 0 c) := by
  have hcomp : Q.toValuationSubring.subtype.comp (algebraMap L Q.toValuationSubring)
      = algebraMap L F := RingHom.ext fun a => rfl
  have hmap : (P.map (mapRingHom (algebraMap L Q.toValuationSubring))).map
      (mapRingHom Q.toValuationSubring.subtype) = P.map (mapRingHom (algebraMap L F)) := by
    rw [Polynomial.map_map]
    congr 1
    refine RingHom.ext fun q => ?_
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_map, hcomp]
  set E := (P.map (mapRingHom (algebraMap L Q.toValuationSubring))).evalEval ⟨z, hz⟩ ⟨f, hf⟩
    with hEdef
  have key : Q.toValuationSubring.subtype E
      = (P.map (mapRingHom (algebraMap L F))).evalEval z f := by
    rw [hEdef, ← map_mapRingHom_evalEval Q.toValuationSubring.subtype, hmap]
    rfl
  have hE : (⟨_, hP⟩ : Q.toValuationSubring) = E := Subtype.ext key.symm
  rw [hE, hEdef, ← map_mapRingHom_evalEval (IsLocalRing.residue Q.toValuationSubring),
    Polynomial.map_map]
  have hz0 : IsLocalRing.residue Q.toValuationSubring ⟨z, hz⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (plane_mem_maximalIdeal_of_ord_pos Q hz hz1)
  have hfcmem : f - algebraMap L F c ∈ Q.toValuationSubring := sub_mem hf (Q.algebraMap_mem' c)
  have hf0 : IsLocalRing.residue Q.toValuationSubring ⟨f, hf⟩
      = algebraMap L Q.ResidueField c := by
    have h1 : IsLocalRing.residue Q.toValuationSubring ⟨f - algebraMap L F c, hfcmem⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr (plane_mem_maximalIdeal_of_ord_pos Q hfcmem hfc)
    have h2 : (⟨f, hf⟩ : Q.toValuationSubring)
        = ⟨f - algebraMap L F c, hfcmem⟩ + algebraMap L Q.toValuationSubring c := by
      ext; simp
    rw [h2, map_add, h1, zero_add]
    rfl
  rw [hz0, hf0]
  have hcomp2 : (IsLocalRing.residue Q.toValuationSubring).comp
      (algebraMap L Q.toValuationSubring) = algebraMap L Q.ResidueField :=
    RingHom.ext fun a => rfl
  have hmap2 : P.map ((mapRingHom (IsLocalRing.residue Q.toValuationSubring)).comp
      (mapRingHom (algebraMap L Q.toValuationSubring)))
      = P.map (mapRingHom (algebraMap L Q.ResidueField)) := by
    congr 1
    refine RingHom.ext fun q => ?_
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_map, hcomp2]
  rw [hmap2, ← map_mapRingHom_evalEval (algebraMap L Q.ResidueField), map_zero]

private theorem plane_exists_poly_of_mem_adjoin (f z : F) {b : F}
    (hb : b ∈ Algebra.adjoin L ({f, z} : Set F)) :
    ∃ P : Polynomial (Polynomial L), b = (P.map (mapRingHom (algebraMap L F))).evalEval z f := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨X, by rw [hx, Polynomial.map_X, evalEval_X]⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨C X, by
        rw [hx, Polynomial.map_C, coe_mapRingHom, Polynomial.map_X, evalEval_C, eval_X]⟩
  | algebraMap r =>
    exact ⟨C (C r), by rw [Polynomial.map_C, coe_mapRingHom, Polynomial.map_C, evalEval_CC]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨P, hP⟩ := ihx
    obtain ⟨R, hR⟩ := ihy
    exact ⟨P + R, by rw [Polynomial.map_add, evalEval_add, ← hP, ← hR]⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨P, hP⟩ := ihx
    obtain ⟨R, hR⟩ := ihy
    exact ⟨P * R, by rw [Polynomial.map_mul, evalEval_mul, ← hP, ← hR]⟩

private theorem plane_evalEval_mem (Q : AlgebraicCurve.Place L F) {z f : F}
    (hz : z ∈ Q.toValuationSubring) (hf : f ∈ Q.toValuationSubring)
    (P : Polynomial (Polynomial L)) :
    (P.map (mapRingHom (algebraMap L F))).evalEval z f ∈ Q.toValuationSubring := by
  have hcomp : Q.toValuationSubring.subtype.comp (algebraMap L Q.toValuationSubring)
      = algebraMap L F := RingHom.ext fun a => rfl
  have hmap : (P.map (mapRingHom (algebraMap L Q.toValuationSubring))).map
      (mapRingHom Q.toValuationSubring.subtype) = P.map (mapRingHom (algebraMap L F)) := by
    rw [Polynomial.map_map]
    congr 1
    refine RingHom.ext fun q => ?_
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_map, hcomp]
  have key := map_mapRingHom_evalEval Q.toValuationSubring.subtype
    (P.map (mapRingHom (algebraMap L Q.toValuationSubring))) ⟨z, hz⟩ ⟨f, hf⟩
  rw [hmap] at key
  have hkey : (P.map (mapRingHom (algebraMap L F))).evalEval z f
      = Q.toValuationSubring.subtype ((P.map (mapRingHom
          (algebraMap L Q.toValuationSubring))).evalEval ⟨z, hz⟩ ⟨f, hf⟩) := key
  rw [hkey]
  exact SetLike.coe_mem _

end Places

section Generic

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]
variable {B : Type*} [CommRing B] [Algebra L B]

private theorem plane_evalEval_mem_adjoin (zB xB : B) (P : Polynomial (Polynomial L)) :
    (P.map (mapRingHom (algebraMap L B))).evalEval zB xB ∈ Algebra.adjoin L (insert xB {zB}) := by
  have hx : xB ∈ Algebra.adjoin L (insert xB ({zB} : Set B)) :=
    Algebra.subset_adjoin (Set.mem_insert _ _)
  have hz : zB ∈ Algebra.adjoin L (insert xB ({zB} : Set B)) :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, evalEval_add]; exact add_mem hp hq
  | monomial n a =>
    rw [Polynomial.map_monomial, ← C_mul_X_pow_eq_monomial, evalEval_mul, evalEval_C, evalEval_pow,
      evalEval_X]
    refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hx _)
    rw [coe_mapRingHom, eval_map]
    induction a using Polynomial.induction_on' with
    | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
    | monomial m r =>
      rw [eval₂_monomial]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) (Subalgebra.pow_mem _ hz _)

private theorem plane_ci_core {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (𝔪 : Ideal B) [𝔪.IsPrime]
    (hprin : (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)).IsPrincipal) (n d : B) :
    ∃ b t : B, t ∉ 𝔪 ∧ (n * b = d * t ∨ d * b = n * t) := by
  have hval : ValuationRing (Localization.AtPrime 𝔪) := by
    have h := (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Localization.AtPrime 𝔪)).out 4 1
    exact h.mp hprin
  have hinj : Function.Injective (algebraMap B (Localization.AtPrime 𝔪)) :=
    IsLocalization.injective (Localization.AtPrime 𝔪) 𝔪.primeCompl_le_nonZeroDivisors
  obtain ⟨q, hq⟩ := ValuationRing.cond (algebraMap B (Localization.AtPrime 𝔪) n)
    (algebraMap B (Localization.AtPrime 𝔪) d)
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq 𝔪.primeCompl q
  refine ⟨b, t, fun ht => t.2 ht, ?_⟩
  rcases hq with hq | hq
  · left
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at hq
    exact hinj hq
  · right
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at hq
    exact hinj hq

private theorem plane_ci_generic [IsDomain B] [IsNoetherianRing B]
    (Q : AlgebraicCurve.Place L F) (c : L) (zB xB : B) (φ : B →+* F)
    (hφL : ∀ a : L, φ (algebraMap L B a) = algebraMap L F a)
    (hφO : ∀ b : B, φ b ∈ Q.toValuationSubring)
    (hzpos : 0 < Q.ord (φ zB)) (hQ : 0 < Q.ord (φ xB - algebraMap L F c))
    (G : Polynomial (Polynomial L))
    (hG : (G.map (mapRingHom (algebraMap L B))).evalEval zB xB = 0)
    (hG0 : G.evalEval 0 c = 0) (hG' : (Polynomial.derivative G).evalEval 0 c ≠ 0)
    (hsurj : ∀ b : B, ∃ P : Polynomial (Polynomial L),
      b = (P.map (mapRingHom (algebraMap L B))).evalEval zB xB)
    (g : F) (hg : g ∈ Q.toValuationSubring) (n d : B) (hd : φ d ≠ 0)
    (hgnd : g = φ n / φ d) :
    ∃ s p : Polynomial (Polynomial L), s.evalEval 0 c ≠ 0 ∧
      g * φ ((s.map (mapRingHom (algebraMap L B))).evalEval zB xB)
        = φ ((p.map (mapRingHom (algebraMap L B))).evalEval zB xB) := by
  classical

  have hcomp : φ.comp (algebraMap L B) = algebraMap L F := RingHom.ext hφL
  have hφev : ∀ P : Polynomial (Polynomial L),
      φ ((P.map (mapRingHom (algebraMap L B))).evalEval zB xB)
        = (P.map (mapRingHom (algebraMap L F))).evalEval (φ zB) (φ xB) := by
    intro P
    have hmap : (P.map (mapRingHom (algebraMap L B))).map (mapRingHom φ)
        = P.map (mapRingHom (algebraMap L F)) := by
      rw [Polynomial.map_map]
      congr 1
      refine RingHom.ext fun q => ?_
      simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_map, hcomp]
    rw [← map_mapRingHom_evalEval φ, hmap]

  set ι : B →+* Q.toValuationSubring := φ.codRestrict Q.toValuationSubring hφO with hιdef
  set 𝔪 : Ideal B := (IsLocalRing.maximalIdeal Q.toValuationSubring).comap ι with h𝔪def
  haveI h𝔪p : 𝔪.IsPrime := Ideal.comap_isPrime ι _
  have hmem : ∀ b : B, b ∈ 𝔪 ↔
      (⟨φ b, hφO b⟩ : Q.toValuationSubring) ∈ IsLocalRing.maximalIdeal Q.toValuationSubring :=
    fun b => Iff.rfl

  have hcrit : ∀ (b : B) (P : Polynomial (Polynomial L)),
      b = (P.map (mapRingHom (algebraMap L B))).evalEval zB xB →
      (b ∈ 𝔪 ↔ P.evalEval 0 c = 0) := by
    intro b P hbP
    have hPO : (P.map (mapRingHom (algebraMap L F))).evalEval (φ zB) (φ xB)
        ∈ Q.toValuationSubring := by
      rw [← hφev]; exact hφO _
    have hb : (⟨φ b, hφO b⟩ : Q.toValuationSubring) = ⟨_, hPO⟩ :=
      Subtype.ext ((congrArg φ hbP).trans (hφev P))
    rw [hmem, ← IsLocalRing.residue_eq_zero_iff, hb,
      plane_residue_evalEval Q c (hφO zB) (hφO xB) hzpos hQ P hPO,
      map_eq_zero_iff _ (RingHom.injective _)]
  have hz𝔪 : zB ∈ 𝔪 := by
    rw [hcrit zB (C X) (by simp [evalEval_C])]
    rw [evalEval_C, eval_X]
  have hx𝔪 : xB - algebraMap L B c ∈ 𝔪 := by
    rw [hcrit (xB - algebraMap L B c) (X - C (C c)) (by simp)]
    rw [evalEval_sub, evalEval_X, evalEval_CC, sub_self]

  haveI h𝔪max : 𝔪.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => ?_, fun J b hJ hb hbJ => ?_⟩
    · rw [hcrit 1 1 (by simp), evalEval_one] at h1
      exact one_ne_zero h1
    · obtain ⟨P, hP⟩ := hsurj b
      have hba : b - algebraMap L B (P.evalEval 0 c) ∈ 𝔪 := by
        rw [hcrit (b - algebraMap L B (P.evalEval 0 c)) (P - C (C (P.evalEval 0 c)))
          (by rw [Polynomial.map_sub, evalEval_sub, ← hP]; simp)]
        rw [evalEval_sub, evalEval_CC, sub_self]
      have ha0 : P.evalEval 0 c ≠ 0 := by
        intro h0
        apply hb
        rw [h0, map_zero, sub_zero] at hba
        exact hba
      have haJ : algebraMap L B (P.evalEval 0 c) ∈ J := by
        have := J.sub_mem hbJ (hJ hba)
        rwa [sub_sub_cancel] at this
      have := J.mul_mem_left (algebraMap L B (P.evalEval 0 c)⁻¹) haJ
      rwa [← map_mul, inv_mul_cancel₀ ha0, map_one] at this

  have hgens : Algebra.adjoin L (insert xB ({zB} : Set B)) = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨P, hP⟩ := hsurj b
    rw [hP]
    exact plane_evalEval_mem_adjoin zB xB P
  have hrel : ∀ g' ∈ ({zB} : Set B), ∃ s p : Polynomial (Polynomial L), s.evalEval 0 c ≠ 0 ∧
      g' * (s.map (Polynomial.mapRingHom (algebraMap L B))).evalEval zB xB
        = (p.map (Polynomial.mapRingHom (algebraMap L B))).evalEval zB xB := by
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    rw [hg']
    refine ⟨1, C X, by rw [evalEval_one]; exact one_ne_zero, ?_⟩
    rw [Polynomial.map_one, evalEval_one, mul_one, Polynomial.map_C, coe_mapRingHom,
      Polynomial.map_X, evalEval_C, eval_X]

  have hprin := redint_isPrincipal_of_plane_data 𝔪 zB xB c hz𝔪 hx𝔪 G hG hG0 hG' ({zB} : Set B)
    hgens hrel

  obtain ⟨b, t, ht, hbt⟩ := plane_ci_core 𝔪 hprin n d
  have ht0 : φ t ≠ 0 := by
    intro h0
    apply ht
    rw [hmem]
    have : (⟨φ t, hφO t⟩ : Q.toValuationSubring) = 0 := Subtype.ext h0
    rw [this]
    exact Ideal.zero_mem _
  have hordt : Q.ord (φ t) = 0 := by
    have h0 : 0 ≤ Q.ord (φ t) := (redint_mem_iff_ord_nonneg Q _).mp (hφO t)
    rcases h0.lt_or_eq with h1 | h1
    · exact absurd ((hmem t).mpr (plane_mem_maximalIdeal_of_ord_pos Q (hφO t) h1)) ht
    · exact h1.symm

  have hfinish : ∀ (t b : B), t ∉ 𝔪 → g * φ t = φ b →
      ∃ s p : Polynomial (Polynomial L), s.evalEval 0 c ≠ 0 ∧
        g * φ ((s.map (mapRingHom (algebraMap L B))).evalEval zB xB)
          = φ ((p.map (mapRingHom (algebraMap L B))).evalEval zB xB) := by
    intro t b ht htb
    obtain ⟨Pt, hPt⟩ := hsurj t
    obtain ⟨Pb, hPb⟩ := hsurj b
    exact ⟨Pt, Pb, fun h0 => ht ((hcrit t Pt hPt).mpr h0), by rw [← hPt, ← hPb]; exact htb⟩
  rcases hbt with hq | hq
  ·
    have hq' : φ n * φ b = φ d * φ t := by rw [← map_mul, ← map_mul, hq]
    have hb0 : φ b ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hq'
      exact mul_ne_zero hd ht0 hq'.symm
    have hgtb : g * φ b = φ t := by
      rw [hgnd, div_mul_eq_mul_div, hq', mul_div_cancel_left₀ _ hd]
    have hb𝔪 : b ∉ 𝔪 := by
      intro hbm
      have hbpos : 0 < Q.ord (φ b) :=
        plane_ord_pos_of_mem_maximalIdeal Q (hφO b) hb0 ((hmem b).mp hbm)
      have hordg : Q.ord g = Q.ord (φ t) - Q.ord (φ b) := by
        have : g = φ t * (φ b)⁻¹ := by
          rw [← hgtb, mul_inv_cancel_right₀ hb0]
        rw [this, Q.ord_mul ht0 (inv_ne_zero hb0), Q.ord_inv]; ring
      have h0 : 0 ≤ Q.ord g := (redint_mem_iff_ord_nonneg Q g).mp hg
      rw [hordg, hordt] at h0
      omega
    exact hfinish b t hb𝔪 hgtb
  ·
    have hq' : φ d * φ b = φ n * φ t := by rw [← map_mul, ← map_mul, hq]
    have hgtb : g * φ t = φ b := by
      rw [hgnd, div_mul_eq_mul_div, ← hq', mul_div_cancel_left₀ _ hd]
    exact hfinish t b ht hgtb

end Generic

section Model

variable (L : Type u) [Field L] {F : Type v} [Field F] [Algebra L F]

private noncomputable def plane_ci_eval (z f : F) : Polynomial (Polynomial L) →+* F :=
  (evalEvalRingHom z f).comp (mapRingHom (mapRingHom (algebraMap L F)))

private def RelationQuotient (z f : F) : Type u :=
  Polynomial (Polynomial L) ⧸ RingHom.ker (plane_ci_eval L z f)

variable {L}

private theorem plane_ci_eval_apply (z f : F) (P : Polynomial (Polynomial L)) :
    plane_ci_eval L z f P = (P.map (mapRingHom (algebraMap L F))).evalEval z f := rfl

private noncomputable scoped instance RelationQuotient.instCommRing (z f : F) : CommRing (RelationQuotient L z f) :=
  inferInstanceAs (CommRing (Polynomial (Polynomial L) ⧸ RingHom.ker (plane_ci_eval L z f)))

p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg.RelationQuotient"
private noncomputable scoped instance RelationQuotient.instAlgebra (z f : F) : Algebra L (RelationQuotient L z f) :=
  inferInstanceAs (Algebra L (Polynomial (Polynomial L) ⧸ RingHom.ker (plane_ci_eval L z f)))

p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg.RelationQuotient"
private scoped instance RelationQuotient.instIsDomain (z f : F) : IsDomain (RelationQuotient L z f) :=
  haveI : (RingHom.ker (plane_ci_eval L z f)).IsPrime := RingHom.ker_isPrime _
  inferInstanceAs (IsDomain (Polynomial (Polynomial L) ⧸ RingHom.ker (plane_ci_eval L z f)))

p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg.RelationQuotient"
private scoped instance RelationQuotient.instIsNoetherianRing (z f : F) : IsNoetherianRing (RelationQuotient L z f) :=
  inferInstanceAs (IsNoetherianRing (Polynomial (Polynomial L) ⧸ RingHom.ker (plane_ci_eval L z f)))

p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg.RelationQuotient"

private noncomputable def relationMk (z f : F) : Polynomial (Polynomial L) →+* RelationQuotient L z f :=
  Ideal.Quotient.mk (RingHom.ker (plane_ci_eval L z f))

private noncomputable def relationLift (z f : F) : RelationQuotient L z f →+* F :=
  RingHom.kerLift (plane_ci_eval L z f)

private theorem relationMk_surjective (z f : F) : Function.Surjective (relationMk (L := L) z f) :=
  Ideal.Quotient.mk_surjective

private theorem relationLift_paMk (z f : F) (P : Polynomial (Polynomial L)) :
    relationLift z f (relationMk z f P) = (P.map (mapRingHom (algebraMap L F))).evalEval z f :=
  RingHom.kerLift_mk (plane_ci_eval L z f) P

private theorem relationLift_injective (z f : F) : Function.Injective (relationLift (L := L) z f) :=
  RingHom.kerLift_injective (plane_ci_eval L z f)

private theorem plane_algebraMap_PaB (z f : F) :
    algebraMap L (RelationQuotient L z f) = (relationMk z f).comp (algebraMap L (Polynomial (Polynomial L))) :=
  rfl

private theorem plane_ci_evalEval_C_X_X (P : Polynomial (Polynomial L)) :
    (P.map (mapRingHom (algebraMap L (Polynomial (Polynomial L))))).evalEval (C X) X = P := by
  rw [Polynomial.evalEval, Polynomial.eval_map]
  exact Polynomial.eval_C_X_eval₂_map_C_X

private theorem plane_evalEval_paMk (z f : F) (P : Polynomial (Polynomial L)) :
    (P.map (mapRingHom (algebraMap L (RelationQuotient L z f)))).evalEval (relationMk z f (C X)) (relationMk z f X)
      = relationMk z f P := by
  rw [plane_algebraMap_PaB, ← Polynomial.mapRingHom_comp, ← Polynomial.map_map,
    map_mapRingHom_evalEval, plane_ci_evalEval_C_X_X]

private theorem plane_surj_PaB (z f : F) (b : RelationQuotient L z f) :
    ∃ P : Polynomial (Polynomial L),
      b = (P.map (mapRingHom (algebraMap L (RelationQuotient L z f)))).evalEval (relationMk z f (C X))
        (relationMk z f X) := by
  obtain ⟨P, rfl⟩ := relationMk_surjective z f b
  exact ⟨P, (plane_evalEval_paMk z f P).symm⟩

private theorem relationLift_algebraMap (z f : F) (a : L) :
    relationLift z f (algebraMap L (RelationQuotient L z f) a) = algebraMap L F a := by
  rw [plane_algebraMap_PaB, RingHom.comp_apply, relationLift_paMk,
    IsScalarTower.algebraMap_apply L (Polynomial L) (Polynomial (Polynomial L)),
    Polynomial.algebraMap_eq, Polynomial.algebraMap_eq, Polynomial.map_C, coe_mapRingHom,
    Polynomial.map_C, evalEval_CC]

private theorem relationLift_mem (Q : AlgebraicCurve.Place L F) {z f : F}
    (hz : z ∈ Q.toValuationSubring) (hf : f ∈ Q.toValuationSubring) (b : RelationQuotient L z f) :
    relationLift z f b ∈ Q.toValuationSubring := by
  obtain ⟨P, rfl⟩ := relationMk_surjective z f b
  rw [relationLift_paMk]
  exact plane_evalEval_mem Q hz hf P

private theorem relationLift_paMk_C_X (z f : F) : relationLift z f (relationMk (L := L) z f (C X)) = z := by
  rw [relationLift_paMk, Polynomial.map_C, coe_mapRingHom, Polynomial.map_X, evalEval_C, eval_X]

private theorem relationLift_paMk_X (z f : F) : relationLift z f (relationMk (L := L) z f X) = f := by
  rw [relationLift_paMk, Polynomial.map_X, evalEval_X]

end Model
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg.RelationQuotient"

private theorem redint_exists_coordinate_identity
    {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F] (f : F) (c : L)
    (Q : AlgebraicCurve.Place L F) (hQ : 0 < Q.ord (f - algebraMap L F c))
    (z : F) (hz : Q.ord z = 1) (hgen : IntermediateField.adjoin L ({f, z} : Set F) = ⊤)
    (G : Polynomial (Polynomial L))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap L F))).evalEval z f = 0)
    (hG0 : G.evalEval 0 c = 0) (hG' : (Polynomial.derivative G).evalEval 0 c ≠ 0)
    (g : F) (hg : g ∈ Q.toValuationSubring) :
    ∃ s p : Polynomial (Polynomial L), s.evalEval 0 c ≠ 0 ∧
      g * (s.map (Polynomial.mapRingHom (algebraMap L F))).evalEval z f
        = (p.map (Polynomial.mapRingHom (algebraMap L F))).evalEval z f := by
  classical
  have hzpos : 0 < Q.ord z := by rw [hz]; exact zero_lt_one
  have hzO : z ∈ Q.toValuationSubring := (redint_mem_iff_ord_nonneg Q z).mpr hzpos.le
  have hfcO : f - algebraMap L F c ∈ Q.toValuationSubring :=
    (redint_mem_iff_ord_nonneg Q _).mpr hQ.le
  have hfO : f ∈ Q.toValuationSubring := by
    have := add_mem hfcO (Q.algebraMap_mem' c)
    rwa [sub_add_cancel] at this

  have hGB : (G.map (mapRingHom (algebraMap L (RelationQuotient L z f)))).evalEval (relationMk z f (C X))
      (relationMk z f X) = 0 := by
    rw [plane_evalEval_paMk]
    apply (map_eq_zero_iff (relationLift z f) (relationLift_injective z f)).mp
    rw [relationLift_paMk]
    exact hG

  have hgtop : g ∈ (⊤ : IntermediateField L F) := IntermediateField.mem_top
  rw [← hgen, IntermediateField.mem_adjoin_iff_div] at hgtop
  obtain ⟨n, hn, d, hd, hgnd⟩ := hgtop
  by_cases hg0 : g = 0
  · refine ⟨1, 0, by rw [evalEval_one]; exact one_ne_zero, ?_⟩
    rw [hg0, zero_mul, Polynomial.map_zero, evalEval_zero]
  have hd0 : d ≠ 0 := by
    intro h0; apply hg0; rw [hgnd, h0, div_zero]
  obtain ⟨Pn, hPn⟩ := plane_exists_poly_of_mem_adjoin f z hn
  obtain ⟨Pd, hPd⟩ := plane_exists_poly_of_mem_adjoin f z hd
  have hφn : relationLift z f (relationMk z f Pn) = n := by rw [relationLift_paMk, ← hPn]
  have hφd : relationLift z f (relationMk z f Pd) = d := by rw [relationLift_paMk, ← hPd]
  obtain ⟨s, p, hs, hsp⟩ := plane_ci_generic Q c (relationMk z f (C X)) (relationMk z f X) (relationLift z f)
    (relationLift_algebraMap z f) (relationLift_mem Q hzO hfO) (by rw [relationLift_paMk_C_X]; exact hzpos)
    (by rw [relationLift_paMk_X]; exact hQ) G hGB hG0 hG' (plane_surj_PaB z f) g hg (relationMk z f Pn)
    (relationMk z f Pd) (by rw [hφd]; exact hd0) (by rw [hφn, hφd]; exact hgnd)
  refine ⟨s, p, hs, ?_⟩
  rw [plane_evalEval_paMk, plane_evalEval_paMk, relationLift_paMk, relationLift_paMk] at hsp
  exact hsp

end CoordinateIdentity
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg.RelationQuotient"

theorem solution
    {L : Type u} [Field L] [IsAlgClosed L]
    {F : Type v} [Field F] [Algebra L F]
    (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    {ι : Type*} [Fintype ι] (y : ι → F)
    (hcard : Fintype.card ι = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hyint : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y i ∈ V)
    (hyli : ∀ c : ι → Polynomial L,
      ∑ i, Polynomial.aeval f (c i) * y i = 0 → ∀ i, c i = 0)
    (hysp : ∀ h : F,
      (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → h ∈ V) →
      ∃ c : ι → Polynomial L, h = ∑ i, Polynomial.aeval f (c i) * y i) :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∀ (Fb : Type v) [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
          (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
          Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) →
          Module.finrank
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
            = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F →
          ∃ hyO : ∀ i, y i ∈ R.integers,
            ∀ h : Fb,
              (∀ w : AlgebraicCurve.Place (IsLocalRing.ResidueField A) Fb,
                0 ≤ w.ord (R.residue ⟨f, hfR⟩) → 0 ≤ w.ord h) →
              ∃ q : ι → Polynomial (IsLocalRing.ResidueField A),
                h = ∑ i, Polynomial.aeval (R.residue ⟨f, hfR⟩) (q i) * R.residue ⟨y i, hyO i⟩ := by
  classical
  by_cases hf : Transcendental L f
  swap
  · refine ⟨∅, by simp, ?_⟩
    intro A _ Fb _ _ R hfR htr _
    exfalso
    have halg : IsAlgebraic L f := not_not.mp hf
    have hdeg1 : (minpoly L f).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible halg.isIntegral)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one L f hdeg1
    have hcA : c ∈ A := (R.algebraMap_mem_iff c).mp (by rw [hc]; exact hfR)
    apply htr
    have key : R.residue ⟨f, hfR⟩
        = algebraMap (IsLocalRing.ResidueField A) Fb (IsLocalRing.residue A ⟨c, hcA⟩) := by
      have hval : (⟨f, hfR⟩ : R.integers)
          = ⟨algebraMap L F c, (R.algebraMap_mem_iff c).mpr hcA⟩ := Subtype.ext hc.symm
      rw [hval]
      exact R.residue_algebraMap ⟨c, hcA⟩
    rw [key]
    exact isAlgebraic_algebraMap _

  have hyint' : ∀ i, IsIntegral (Algebra.adjoin L ({f} : Set F)) (y i) := fun i =>
    AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring f f (y i)
      (fun v hv => hyint i v.toValuationSubring (fun c => v.algebraMap_mem' c) hv)
  have hfc : ∀ c : L, f - algebraMap L F c ≠ 0 := fun c h => by
    apply hf
    have : f = algebraMap L F c := sub_eq_zero.mp h
    rw [this]
    exact isAlgebraic_algebraMap c

  obtain ⟨lead, Cs, mlt, hlead0, hdisc⟩ := redint_exists_discr_factorization f hf y hcard hyli hyint'

  have hTfin : ∀ c : L, {Q : AlgebraicCurve.Place L F | 0 < Q.ord (f - algebraMap L F c)}.Finite :=
    fun c => redint_finite_zeros f hf _ (hfc c)
  let T : L → Finset (AlgebraicCurve.Place L F) := fun c => (hTfin c).toFinset
  have hT : ∀ c (Q : AlgebraicCurve.Place L F), Q ∈ T c ↔ 0 < Q.ord (f - algebraMap L F c) :=
    fun c Q => (hTfin c).mem_toFinset

  have hplane := fun (c : L) (Q : AlgebraicCurve.Place L F) (hQ : 0 < Q.ord (f - algebraMap L F c)) =>
    redint_exists_plane_data f hf c Q hQ
  choose! z G hzG using hplane

  have hrad : ∀ c : L, ∃ (N : ℕ) (hr : F),
      (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → hr ∈ V) ∧
      (∏ Q ∈ T c, z c Q) ^ N = (f - algebraMap L F c) * hr := by
    intro c
    refine redint_exists_pow_prod_eq_mul f c (T c) (hT c) (hfc c) (z c) ?_ ?_
    · intro Q hQ
      exact (hzG c Q ((hT c Q).mp hQ)).1
    · intro Q hQ
      rw [(hzG c Q ((hT c Q).mp hQ)).2.1]
      exact zero_lt_one
  choose Nr hr hhr using hrad

  have hyreg : ∀ (c : L) (Q : AlgebraicCurve.Place L F), 0 < Q.ord (f - algebraMap L F c) →
      ∀ i, y i ∈ Q.toValuationSubring := by
    intro c Q hQ i
    refine hyint i Q.toValuationSubring (fun a => Q.algebraMap_mem' a) ?_
    have h1 : f - algebraMap L F c ∈ Q.toValuationSubring := (redint_mem_iff_ord_nonneg Q _).mpr hQ.le
    have h2 : algebraMap L F c ∈ Q.toValuationSubring := Q.algebraMap_mem' c
    simpa using add_mem h1 h2

  have hcoord := fun (c : L) (Q : AlgebraicCurve.Place L F) (hQ : 0 < Q.ord (f - algebraMap L F c)) (i : ι) =>
    redint_exists_coordinate_identity f c Q hQ (z c Q) (hzG c Q hQ).2.1 (hzG c Q hQ).2.2.2.1 (G c Q)
      (hzG c Q hQ).2.2.2.2.1 (hzG c Q hQ).2.2.2.2.2.1 (hzG c Q hQ).2.2.2.2.2.2 (y i) (hyreg c Q hQ i)
  choose! sP pP hsp using hcoord

  choose tab htab using fun i j => hysp (y i * y j)
    (fun V hV hfV => mul_mem (hyint i V hV hfV) (hyint j V hV hfV))
  obtain ⟨onec, honec⟩ := hysp 1 (fun V _ _ => one_mem V)
  choose! zc hzc using fun (c : L) (Q : AlgebraicCurve.Place L F) (hQ : 0 < Q.ord (f - algebraMap L F c)) =>
    hysp (z c Q) (hzG c Q hQ).1
  choose hc hhc using fun c => hysp (hr c) (hhr c).1

  obtain ⟨S₃, hS₃0, hS₃⟩ :=
    AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span
      f y hcard hyint hyli

  let cf : Polynomial L → Finset L := fun p => p.coeffs
  let cf2 : Polynomial (Polynomial L) → Finset L := fun P => P.support.biUnion fun n => (P.coeff n).coeffs
  let cfι : (ι → Polynomial L) → Finset L := fun q => Finset.univ.biUnion fun i => cf (q i)
  let Sraw : Finset L :=
    S₃ ∪ {lead} ∪ Cs ∪ cfι onec ∪ (Finset.univ : Finset (ι × ι)).biUnion (fun ij => cfι (tab ij.1 ij.2)) ∪
      Cs.biUnion (fun c => cfι (hc c) ∪ (T c).biUnion (fun Q =>
        cf2 (G c Q) ∪ {(Polynomial.derivative (G c Q)).evalEval 0 c} ∪ cfι (zc c Q) ∪
          Finset.univ.biUnion (fun i => cf2 (sP c Q i) ∪ cf2 (pP c Q i) ∪ {(sP c Q i).evalEval 0 c})))
  refine ⟨Sraw.filter (· ≠ 0), fun s hs => (Finset.mem_filter.mp hs).2, ?_⟩
  intro A hSA Fb _ _ R hfR htr hdeg
  have hA : ∀ k ∈ Sraw, k ∈ A := by
    intro k hk
    by_cases hk0 : k = 0
    · rw [hk0]; simp
    · exact A.mem_of_valuation_le_one k (hSA k (Finset.mem_filter.mpr ⟨hk, hk0⟩)).le
  have hres : ∀ k ∈ Sraw, k ≠ 0 → ∀ hk : k ∈ A, IsLocalRing.residue A ⟨k, hk⟩ ≠ 0 := by
    intro k hk hk0 hkA
    have hu : IsUnit (⟨k, hkA⟩ : A) :=
      (A.valuation_eq_one_iff ⟨k, hkA⟩).mpr (hSA k (Finset.mem_filter.mpr ⟨hk, hk0⟩))
    exact (hu.map (IsLocalRing.residue A)).ne_zero

  have hcfA : ∀ p : Polynomial L, (∀ k ∈ cf p, k ∈ Sraw) → ∀ n, p.coeff n ∈ A := by
    intro p hp n
    by_cases h0 : p.coeff n = 0
    · rw [h0]; simp
    · exact hA _ (hp _ (Polynomial.mem_coeffs_iff.mpr ⟨n, Polynomial.mem_support_iff.mpr h0, rfl⟩))
  have hcf2A : ∀ P : Polynomial (Polynomial L), (∀ k ∈ cf2 P, k ∈ Sraw) → ∀ n m, (P.coeff n).coeff m ∈ A := by
    intro P hP n m
    by_cases hn : P.coeff n = 0
    · rw [hn]; simp
    · by_cases h0 : (P.coeff n).coeff m = 0
      · rw [h0]; simp
      · refine hA _ (hP _ ?_)
        simp only [cf2, Finset.mem_biUnion]
        exact ⟨n, Polynomial.mem_support_iff.mpr hn,
          Polynomial.mem_coeffs_iff.mpr ⟨m, Polynomial.mem_support_iff.mpr h0, rfl⟩⟩
  have hcfιA : ∀ q : ι → Polynomial L, (∀ k ∈ cfι q, k ∈ Sraw) → ∀ i n, (q i).coeff n ∈ A := by
    intro q hq i
    refine hcfA (q i) (fun k hk => hq k ?_)
    simp only [cfι, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hk⟩
  have hmem_c : ∀ c ∈ Cs, ∀ x, x ∈ cfι (hc c) → x ∈ Sraw := fun c hcs x hx =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hcs, Finset.mem_union_left _ hx⟩)
  have hmem_Q : ∀ c ∈ Cs, ∀ Q ∈ T c, ∀ x,
      x ∈ cf2 (G c Q) ∪ {(Polynomial.derivative (G c Q)).evalEval 0 c} ∪ cfι (zc c Q) ∪
        Finset.univ.biUnion (fun i => cf2 (sP c Q i) ∪ cf2 (pP c Q i) ∪ {(sP c Q i).evalEval 0 c}) →
      x ∈ Sraw := fun c hcs Q hQ x hx =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨c, hcs, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨Q, hQ, hx⟩)⟩)

  have hS₃sub : ∀ s ∈ S₃, s ∈ Sraw := fun s hs => by simp [Sraw, hs]
  obtain ⟨hyO, huniq, hspan₃⟩ := hS₃ A
    (fun s hs => hSA s (Finset.mem_filter.mpr ⟨hS₃sub s hs, hS₃0 s hs⟩)) Fb R hfR htr hdeg
  refine ⟨hyO, ?_⟩

  set fb : Fb := R.residue ⟨f, hfR⟩ with hfb
  set yb : ι → Fb := fun i => R.residue ⟨y i, hyO i⟩ with hyb

  have hredsum : ∀ q : ι → Polynomial L, (∀ i n, (q i).coeff n ∈ A) →
      ∃ qb : ι → Polynomial (IsLocalRing.ResidueField A),
        ∀ hm : (∑ i, Polynomial.aeval f (q i) * y i) ∈ R.integers,
          R.residue ⟨_, hm⟩ = ∑ i, Polynomial.aeval fb (qb i) * yb i :=
    fun q hq => redint_redsum A R hfR y hyO q hq
  have hsum_mem : ∀ q : ι → Polynomial L, (∀ i n, (q i).coeff n ∈ A) →
      (∑ i, Polynomial.aeval f (q i) * y i) ∈ R.integers := fun q hq =>
    sum_mem fun i _ => mul_mem (redint_aeval_mem_integers A R hfR (q i) (hq i)) (hyO i)

  have htabA : ∀ i j, ∀ k n, (tab i j k).coeff n ∈ A := fun i j =>
    hcfιA (tab i j) (fun x hx => by
      simp only [Sraw, Finset.mem_union]
      refine Or.inl (Or.inr ?_)
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨(i, j), hx⟩)
  have honecA : ∀ i n, (onec i).coeff n ∈ A := hcfιA onec (fun x hx => by simp [Sraw, hx])
  have htabb : ∀ i j, ∃ t : ι → Polynomial (IsLocalRing.ResidueField A),
      yb i * yb j = ∑ k, Polynomial.aeval fb (t k) * yb k := by
    intro i j
    obtain ⟨t, ht⟩ := hredsum (tab i j) (htabA i j)
    refine ⟨t, ?_⟩
    rw [← ht (hsum_mem _ (htabA i j))]
    simp only [hyb]
    rw [← map_mul]
    congr 1
    exact Subtype.ext (htab i j)
  choose tabb htabb using htabb
  have honeb : ∃ u : ι → Polynomial (IsLocalRing.ResidueField A),
      (1 : Fb) = ∑ k, Polynomial.aeval fb (u k) * yb k := by
    obtain ⟨u, hu⟩ := hredsum onec honecA
    refine ⟨u, ?_⟩
    rw [← hu (hsum_mem _ honecA), ← map_one R.residue]
    congr 1
    exact Subtype.ext honec
  obtain ⟨oneb, honeb⟩ := honeb

  let Mb : Subalgebra (IsLocalRing.ResidueField A) Fb := Algebra.adjoin _ (insert fb (Set.range yb))
  have hfbM : fb ∈ Mb := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hybM : ∀ i, yb i ∈ Mb := fun i => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  have hsumM : ∀ q : ι → Polynomial (IsLocalRing.ResidueField A), (∑ i, Polynomial.aeval fb (q i) * yb i) ∈ Mb :=
    fun q => sum_mem fun i _ => mul_mem
      ((Algebra.adjoin_le (Set.singleton_subset_iff.mpr hfbM)) (Polynomial.aeval_mem_adjoin_singleton _ fb)) (hybM i)
  have hMspan : ∀ m ∈ Mb, ∃ q : ι → Polynomial (IsLocalRing.ResidueField A),
      m = ∑ i, Polynomial.aeval fb (q i) * yb i :=
    redint_span_of_adjoin fb yb tabb htabb oneb honeb

  obtain ⟨hdO, hdres⟩ := redint_residue_discr f R hfR htr hdeg y hyO
  have hleadA : lead ∈ A := hA lead (by simp [Sraw])
  have hCsA : ∀ c ∈ Cs, c ∈ A := fun c hcs => hA c (by simp [Sraw, hcs])
  let cA : L → A := fun c => if h : c ∈ A then ⟨c, h⟩ else 0
  have hcA_coe : ∀ c ∈ A, ((cA c : A) : L) = c := fun c h => by simp [cA, h]
  let κb : L → Fb := fun c => algebraMap (IsLocalRing.ResidueField A) Fb (IsLocalRing.residue A (cA c))
  have hΔfact : (Algebra.discr (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({fb} : Set Fb)) yb : Fb)
      = algebraMap (IsLocalRing.ResidueField A) Fb (IsLocalRing.residue A (cA lead)) *
        ∏ c ∈ Cs, (fb - algebraMap (IsLocalRing.ResidueField A) Fb (IsLocalRing.residue A (cA c))) ^ mlt c :=
    redint_residue_factorization R hfR hdO hdres hdisc cA (fun c h => by simp [cA, h]) hleadA hCsA
  set Δ : Fb :=
    (Algebra.discr (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({fb} : Set Fb)) yb : Fb) with hΔdef
  have hκbM : ∀ c, κb c ∈ Mb := fun c => Subalgebra.algebraMap_mem Mb _
  have hΔM : Δ ∈ Mb := by
    rw [hΔfact]
    exact mul_mem (hκbM lead) (prod_mem fun c _ => pow_mem (sub_mem hfbM (hκbM c)) _)
  have hκb_ne : ∀ k ∈ Sraw, k ≠ 0 → κb k ≠ 0 := by
    intro k hk hk0
    have hkA := hA k hk
    have h1 : IsLocalRing.residue A (cA k) ≠ 0 := by
      have : cA k = ⟨k, hkA⟩ := by simp [cA, hkA]
      rw [this]; exact hres k hk hk0 hkA
    exact (map_ne_zero_iff _ (algebraMap (IsLocalRing.ResidueField A) Fb).injective).mpr h1
  have hfb_sub_ne : ∀ c : L, fb - κb c ≠ 0 := fun c h => htr (by
    have : fb = κb c := sub_eq_zero.mp h
    rw [this]; exact isAlgebraic_algebraMap _)
  have hΔ0 : Δ ≠ 0 := by
    rw [hΔfact]
    refine mul_ne_zero (hκb_ne lead (by simp [Sraw]) hlead0)
      (Finset.prod_ne_zero_iff.mpr fun c _ => pow_ne_zero _ (hfb_sub_ne c))
  have hfg : Mb.FG := (Subalgebra.fg_def).mpr ⟨_, (Set.finite_range yb).insert fb, rfl⟩

  have hprin : ∀ (𝔪 : Ideal Mb) [𝔪.IsMaximal], (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)).IsPrincipal := by
    intro 𝔪 h𝔪
    by_cases hΔm : (⟨Δ, hΔM⟩ : Mb) ∈ 𝔪
    ·
      have hlead_res : IsLocalRing.residue A (cA lead) ≠ 0 := by
        have : cA lead = ⟨lead, hleadA⟩ := by simp [cA, hleadA]
        rw [this]; exact hres lead (by simp [Sraw]) hlead0 hleadA
      obtain ⟨c, hcCs, hcm⟩ : ∃ c ∈ Cs, (⟨fb, hfbM⟩ : Mb) - algebraMap _ Mb (IsLocalRing.residue A (cA c)) ∈ 𝔪 :=
        redint_exists_bad_value Mb 𝔪 hΔM hfbM (fun c => IsLocalRing.residue A (cA c)) hΔfact hlead_res hΔm

      have hcA' : c ∈ A := hCsA c hcCs
      have hzO : ∀ Q ∈ T c, z c Q ∈ R.integers := fun Q hQ => by
        have hQ' := (hT c Q).mp hQ
        rw [hzc c Q hQ']
        exact hsum_mem _ (hcfιA (zc c Q) (fun x hx =>
          hmem_Q c hcCs Q hQ x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))))
      have hhrO : hr c ∈ R.integers := by
        rw [hhc c]
        exact hsum_mem _ (hcfιA (hc c) (fun x hx => hmem_c c hcCs x hx))
      have hzM : ∀ Q ∈ T c, ∀ hQO : z c Q ∈ R.integers, R.residue ⟨z c Q, hQO⟩ ∈ Mb := by
        intro Q hQ hQO
        have hQ' := (hT c Q).mp hQ
        obtain ⟨qb, hqb⟩ := hredsum (zc c Q) (hcfιA (zc c Q) (fun x hx =>
          hmem_Q c hcCs Q hQ x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))))
        have e : (⟨z c Q, hQO⟩ : R.integers)
            = ⟨_, hsum_mem _ (hcfιA (zc c Q) (fun x hx =>
                hmem_Q c hcCs Q hQ x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))))⟩ :=
          Subtype.ext (hzc c Q hQ')
        rw [e, hqb]
        exact hsumM qb
      have hhrM : R.residue ⟨hr c, hhrO⟩ ∈ Mb := by
        obtain ⟨qb, hqb⟩ := hredsum (hc c) (hcfιA (hc c) (fun x hx => hmem_c c hcCs x hx))
        have e : (⟨hr c, hhrO⟩ : R.integers) = ⟨_, hsum_mem _ (hcfιA (hc c) (fun x hx => hmem_c c hcCs x hx))⟩ :=
          Subtype.ext (hhc c)
        rw [e, hqb]
        exact hsumM qb
      have hcm' : (⟨fb, hfbM⟩ : Mb) - algebraMap _ Mb (IsLocalRing.residue A ⟨c, hcA'⟩) ∈ 𝔪 := by
        have : cA c = ⟨c, hcA'⟩ := by simp [cA, hcA']
        rw [← this]; exact hcm
      obtain ⟨Q, hQT, hzm⟩ :=
        redint_reduced_radical R hfR Mb 𝔪 hfbM hzO (fun Q hQ => hzM Q hQ (hzO Q hQ)) hhrO hhrM hcA' (hhr c).2 hcm'
      have hQ' := (hT c Q).mp hQT
      obtain ⟨-, -, -, -, hGrel, hG0, hG'⟩ := hzG c Q hQ'
      have hδmem : (Polynomial.derivative (G c Q)).evalEval 0 c ∈ Sraw :=
        hmem_Q c hcCs Q hQT _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_singleton_self _))))
      have hδA : (Polynomial.derivative (G c Q)).evalEval 0 c ∈ A := hA _ hδmem
      have hs0mem : ∀ i, (sP c Q i).evalEval 0 c ∈ Sraw := fun i =>
        hmem_Q c hcCs Q hQT _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩))
      have hs0A : ∀ i, (sP c Q i).evalEval 0 c ∈ A := fun i => hA _ (hs0mem i)
      exact redint_bad_value_principal R hfR Mb 𝔪 y hyO hybM hfbM rfl hcA' (hzO Q hQT) (hzM Q hQT _) hzm hcm'
        (G c Q)
        (hcf2A (G c Q) (fun x hx => hmem_Q c hcCs Q hQT x
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))))
        hGrel hG0 hδA (hres _ hδmem hG' hδA)
        (sP c Q) (pP c Q)
        (fun i => hcf2A (sP c Q i) (fun x hx => hmem_Q c hcCs Q hQT x
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_union_left _ hx)⟩))))
        (fun i => hcf2A (pP c Q i) (fun x hx => hmem_Q c hcCs Q hQT x
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_union_right _ hx)⟩))))
        (fun i => (hsp c Q hQ' i).2) hs0A (fun i => hres _ (hs0mem i) (hsp c Q hQ' i).1 (hs0A i))
    ·
      refine redint_isPrincipal_of_discr_not_mem Mb fb hfbM htr yb hybM hfg hMspan ?_ ?_ Δ hΔdef hΔM 𝔪 hΔm
      · refine redint_linearIndependent htr yb ?_
        intro q hq i
        have := huniq q 0 (by simpa using hq)
        rw [this]; rfl
      · exact redint_span_eq_top fb yb hspan₃

  intro hh hreg
  have hcardpos : 0 < Fintype.card ι := by rw [hcard]; exact Module.finrank_pos
  haveI : Nonempty ι := Fintype.card_pos_iff.mp hcardpos
  haveI hfin : FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({fb} : Set Fb)) Fb :=
    FiniteDimensional.of_finrank_pos (by rw [hdeg, ← hcard]; exact hcardpos)
  haveI hsep : Algebra.IsSeparable (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({fb} : Set Fb)) Fb :=
    redint_isSeparable_of_discr_ne_zero yb (fun h => hΔ0 (by rw [hΔdef, h]; simp))
  have hint : IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) ({fb} : Set Fb)) hh :=
    AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring fb fb hh
      (fun v hv => (redint_mem_iff_ord_nonneg v hh).mpr (hreg v ((redint_mem_iff_ord_nonneg v fb).mp hv)))
  have hintM : IsIntegral Mb hh :=
    redint_isIntegral_of_le (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hfbM)) hint
  have hhM : hh ∈ Mb :=
    Subalgebra.mem_of_isIntegral_of_fg_of_forall_isPrincipal_maximalIdeal_localization_atPrime Mb hfg
      (redint_exists_mul_mem Mb fb hfbM htr yb hybM hspan₃) hprin hh hintM
  obtain ⟨q, hq⟩ := hMspan hh hhM
  exact ⟨q, hq⟩

end S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg (solution)
