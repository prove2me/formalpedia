-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.residue_mem_riemannRochSpace_and_evalAt_eq_of_forall_mem_integers_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ed227ee5-8255-5eae-9f0b-a92d3ca7232f

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_residue_mem_riemannRochSpace_and_evalAt_eq_of_forall_mem_integers_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

open AlgebraicCurve

open Classical in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (D : Divisor L F) (hD : ∀ P ∈ D.support, ∃ i, P ∈ (C i).dom)
    :
    ∀ (f : F) (hf : ∀ i, f ∈ (C i).integers), f ≠ 0 → f ∈ riemannRochSpace D →
      (∀ i, (C i).residue ⟨f, hf i⟩ ∈
        riemannRochSpace (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
          Divisor (IsLocalRing.ResidueField A) (Fbar i))) ∧
      ∀ e, (xs e).evalAt ((C (src e)).residue ⟨f, hf (src e)⟩) = (xt e).evalAt ((C (tgt e)).residue ⟨f, hf (tgt e)⟩)  := by
  intro f hf hf0 hfD
  classical
  have _ := hrk; have _ := hgenus; have _ := hdisc; have _ := hw; have _ := hπ0; have _ := hπ; have _ := hratF; have _ := hD
  have hordD : ∀ v : Place L F, -D v ≤ v.ord f := fun v => ((mem_riemannRochSpace_iff.mp hfD) v).resolve_left hf0

  have hDann : ∀ e, ∀ P ∈ (An e).dom, D P = 0 := by
    intro e P hP
    by_contra hne
    obtain ⟨i, hi⟩ := hD P (Finsupp.mem_support_iff.mpr hne)
    rcases hcover P with ⟨j, -, -, hnot⟩ | ⟨e', -, -, hnot⟩
    · exact hnot e hP
    · exact hnot i hi
  have hreg : ∀ e, ∀ P ∈ (An e).dom, 0 ≤ P.ord f := by
    intro e P hP
    have := hordD P
    rw [hDann e P hP, neg_zero] at this
    exact this

  have hann := fun e =>
    AlgebraicCurve.Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached A (An e) (An' e)
      (hpair e).1 (hpair e).2.1 (hpair e).2.2.1 (hpair e).2.2.2 (C (src e)) (xs e) (hratBar _ _) (hatt e).1
      (C (tgt e)) (xt e) (hratBar _ _) (hatt e).2 f (hf (src e)) (hf (tgt e)) (hreg e)
  refine ⟨fun i => ?_, fun e => (hann e).2.2⟩
  by_cases hres : (C i).residue ⟨f, hf i⟩ = 0
  · rw [hres]; exact zero_mem _
  rw [mem_riemannRochSpace_iff]
  refine fun y => Or.inr ?_
  by_cases hy : y ∈ (C i).nodes
  ·
    have hD0 : Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) y = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro h0
      obtain ⟨P, hP, hPy⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h0)
      rw [Finsupp.support_filter, Finset.mem_filter] at hP
      exact (C i).placeMap_not_mem_nodes P hP.2 (hPy ▸ hy)
    rw [hD0, neg_zero]
    obtain ⟨e, h | h⟩ := hnodes.1 i y hy
    · obtain ⟨hse, hxy⟩ := Sigma.mk.inj_iff.mp h
      subst hse
      have hxy' := eq_of_heq hxy
      subst hxy'
      exact (hann e).1 hres
    · obtain ⟨hte, hxy⟩ := Sigma.mk.inj_iff.mp h
      subst hte
      have hxy' := eq_of_heq hxy
      subst hxy'
      exact (hann e).2.1 hres
  ·
    obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0
    have hmap := (C i).mapDomain_placeMap ⟨f, hf i⟩ hres (Df.filter fun P => P ∈ (C i).dom)
      (fun P hP => by rw [Finsupp.filter_apply, if_pos hP, hDf]) (fun P hP => by rw [Finsupp.filter_apply, if_neg hP])
      y hy
    have hnn : ∀ v : Place L F,
        0 ≤ ((D.filter fun P => P ∈ (C i).dom) + Df.filter fun P => P ∈ (C i).dom) v := by
      intro v
      rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
      by_cases hv : v ∈ (C i).dom
      · rw [if_pos hv, if_pos hv, hDf]; linarith [hordD v]
      · rw [if_neg hv, if_neg hv, add_zero]
    have hmapnn : 0 ≤ Finsupp.mapDomain (C i).placeMap
        ((D.filter fun P => P ∈ (C i).dom) + Df.filter fun P => P ∈ (C i).dom) y := by
      simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
      refine Finset.sum_nonneg fun v _ => ?_
      split_ifs
      · exact hnn v
      · exact le_rfl
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, hmap] at hmapnn
    linarith

end S_AlgebraicCurve_SemistableCovering_residue_mem_riemannRochSpace_and_evalAt_eq_of_forall_mem_integers_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_residue_mem_riemannRochSpace_and_evalAt_eq_of_forall_mem_integers_of_rankOne (solution)
