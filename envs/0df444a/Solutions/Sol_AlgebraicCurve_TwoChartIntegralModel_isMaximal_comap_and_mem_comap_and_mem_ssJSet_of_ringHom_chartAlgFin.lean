-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isMaximal_comap_and_mem_comap_and_mem_ssJSet_of_ringHom_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0acb06f4-3496-5416-bd16-4c055a2f5e42

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_forall_apply_mem_ssJSet_of_ker_eq_of_apply_mem_ssJSet
import Theorems.Thm_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isMaximal_comap_and_mem_comap_and_mem_ssJSet_of_ringHom_chartAlgFin
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.jqNModC_one"
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve.TwoChartIntegralModel

open Polynomial in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (A₀ : Type) [CommRing A₀] [IsLocalRing A₀] (A : Type) [CommRing A] [IsLocalRing A]
    [Algebra A₀ A] [IsLocalHom (algebraMap A₀ A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (F₀ : Type) [Field F₀] [Algebra A₀ F₀] (j₀ : F₀) [Fact (j₀ ≠ 0)]
    (F : Type) [Field F] [Algebra A F] (j : F) [Fact (j ≠ 0)]
    (c : ↥(chartAlgFin A₀ F₀ j₀) →+* ↥(chartAlgFin A F j))
    (hcj : c (jChartFin A₀ F₀ j₀) = jChartFin A F j)
    (hcA : ∀ a : A₀, c (algebraMap A₀ ↥(chartAlgFin A₀ F₀ j₀) a) =
      algebraMap A ↥(chartAlgFin A F j) (algebraMap A₀ A a))
    (y : Ideal ↥(chartAlgFin A F j)) (hymax : y.IsMaximal)
    (hyA : Ideal.map (algebraMap A ↥(chartAlgFin A F j)) (IsLocalRing.maximalIdeal A) ≤ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A F j) →+* Ω),
      RingHom.ker φ = y → φ (jChartFin A F j) ∈ ModularCurve.ssJSet q Ω)
    (ϖ₀ : A₀) (hϖ₀ : ϖ₀ ∈ IsLocalRing.maximalIdeal A₀) :
    (Ideal.comap c y).IsMaximal ∧
    algebraMap A₀ ↥(chartAlgFin A₀ F₀ j₀) ϖ₀ ∈ Ideal.comap c y ∧
    (∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(chartAlgFin A₀ F₀ j₀) →+* Ω),
        RingHom.ker φ = Ideal.comap c y → φ (jChartFin A₀ F₀ j₀) ∈ ModularCurve.ssJSet q Ω) := by
  classical
  haveI : y.IsMaximal := hymax

  have hmA₀ : ∀ a ∈ IsLocalRing.maximalIdeal A₀, c (algebraMap A₀ ↥(chartAlgFin A₀ F₀ j₀) a) ∈ y := by
    intro a ha
    rw [hcA]
    apply hyA
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    exact fun hu => ha (isUnit_of_map_unit (algebraMap A₀ A) a hu)

  have hii : algebraMap A₀ ↥(chartAlgFin A₀ F₀ j₀) ϖ₀ ∈ Ideal.comap c y := by
    rw [Ideal.mem_comap]
    exact hmA₀ ϖ₀ hϖ₀

  letI instField : Field (↥(chartAlgFin A F j) ⧸ y) := Ideal.Quotient.field y
  obtain ⟨φC, hφC⟩ : ∃ φC : ↥(chartAlgFin A F j) →+* AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y),
      φC = (algebraMap (↥(chartAlgFin A F j) ⧸ y) (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y))).comp (Ideal.Quotient.mk y) := ⟨_, rfl⟩
  have hkerφC : RingHom.ker φC = y := by
    ext x
    rw [RingHom.mem_ker, hφC, RingHom.comp_apply,
      map_eq_zero_iff _ (algebraMap (↥(chartAlgFin A F j) ⧸ y) (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y))).injective,
      Ideal.Quotient.eq_zero_iff_mem]

  have hqy : algebraMap A ↥(chartAlgFin A F j) (q : A) ∈ y := hyA (Ideal.mem_map_of_mem _ hAq)
  have hqκ : ((q : ℕ) : ↥(chartAlgFin A F j) ⧸ y) = 0 := by
    have : Ideal.Quotient.mk y (algebraMap A ↥(chartAlgFin A F j) (q : A)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqy
    simpa using this
  haveI : CharP (↥(chartAlgFin A F j) ⧸ y) q := (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr hqκ
  haveI : CharP (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y)) q := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr ?_
    have := congrArg (algebraMap (↥(chartAlgFin A F j) ⧸ y) (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y))) hqκ
    simpa using this
  have hφCj : φC (jChartFin A F j) ∈ ModularCurve.ssJSet q (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y)) :=
    hss _ φC hkerφC

  have hiii : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A₀ F₀ j₀) →+* Ω), RingHom.ker φ = Ideal.comap c y →
        φ (jChartFin A₀ F₀ j₀) ∈ ModularCurve.ssJSet q Ω := by
    have hker0 : RingHom.ker (φC.comp c) = Ideal.comap c y := by
      rw [← RingHom.comap_ker, hkerφC]
    have h0 : (φC.comp c) (jChartFin A₀ F₀ j₀) ∈ ModularCurve.ssJSet q (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y)) := by
      rw [RingHom.comp_apply, hcj]; exact hφCj
    intro Ω _ _ _ _ φ hφ
    exact ModularCurve.forall_apply_mem_ssJSet_of_ker_eq_of_apply_mem_ssJSet q (jChartFin A₀ F₀ j₀)
      (φC.comp c) h0 Ω φ (hφ.trans hker0.symm)

  have hi : (Ideal.comap c y).IsMaximal := by

    set θ : Polynomial A₀ →+* ↥(chartAlgFin A₀ F₀ j₀) := (polynomialToChartFin A₀ F₀ j₀).toRingHom with hθ
    have hθX : θ X = jChartFin A₀ F₀ j₀ := by
      rw [hθ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, polynomialToChartFin_X]
    have hθC : ∀ a : A₀, θ (C a) = algebraMap A₀ ↥(chartAlgFin A₀ F₀ j₀) a := by
      intro a
      rw [hθ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      show Polynomial.aeval (jChartFin A₀ F₀ j₀) (C a) = _
      rw [aeval_C]
    have hθint : θ.IsIntegral := by
      intro x

      have hx : IsIntegral ↥(Algebra.adjoin A₀ ({j₀} : Set F₀)) (x : F₀) := (mem_chartAlg_iff A₀ F₀).mp x.2
      obtain ⟨P, hPm, hPx⟩ := hx

      have hmemρ : ∀ p : Polynomial A₀, Polynomial.aeval j₀ p ∈ Algebra.adjoin A₀ ({j₀} : Set F₀) := by
        intro p
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨p, rfl⟩
      set ρ : Polynomial A₀ →+* ↥(Algebra.adjoin A₀ ({j₀} : Set F₀)) :=
        (Polynomial.aeval j₀ : Polynomial A₀ →ₐ[A₀] F₀).toRingHom.codRestrict
          (Algebra.adjoin A₀ ({j₀} : Set F₀)).toSubring (fun p => hmemρ p) with hρ
      have hρsurj : Function.Surjective ρ := by
        rintro ⟨z, hz⟩
        rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
        obtain ⟨p, rfl⟩ := hz
        exact ⟨p, rfl⟩
      have hρval : (algebraMap ↥(Algebra.adjoin A₀ ({j₀} : Set F₀)) F₀).comp ρ =
          ((chartAlgFin A₀ F₀ j₀).val.toRingHom).comp θ := by
        apply Polynomial.ringHom_ext
        · intro a
          rw [RingHom.comp_apply, RingHom.comp_apply, hθC]
          show Polynomial.aeval j₀ (C a) = ((algebraMap A₀ ↥(chartAlgFin A₀ F₀ j₀) a : ↥(chartAlgFin A₀ F₀ j₀)) : F₀)
          rw [aeval_C]
          rfl
        · rw [RingHom.comp_apply, RingHom.comp_apply, hθX]
          show Polynomial.aeval j₀ X = ((jChartFin A₀ F₀ j₀ : ↥(chartAlgFin A₀ F₀ j₀)) : F₀)
          rw [aeval_X, coe_jChartFin]
      obtain ⟨Q, hQP, -, hQm⟩ := lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective hρsurj P) hPm
      refine ⟨Q, hQm, ?_⟩
      apply Subtype.val_injective
      show ((chartAlgFin A₀ F₀ j₀).val.toRingHom) (Q.eval₂ θ x) = ((0 : ↥(chartAlgFin A₀ F₀ j₀)) : F₀)
      rw [hom_eval₂, ← hρval, ← eval₂_map, hQP]
      exact hPx

    set f : A₀ →+* (↥(chartAlgFin A F j) ⧸ y) := (Ideal.Quotient.mk y).comp (c.comp (algebraMap A₀ ↥(chartAlgFin A₀ F₀ j₀))) with hf
    haveI hfloc : IsLocalHom f := by
      constructor
      intro a ha
      by_contra hna
      have hmem : a ∈ IsLocalRing.maximalIdeal A₀ := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hna
      have : f a = 0 := by
        rw [hf, RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hmA₀ a hmem
      rw [this] at ha
      exact not_isUnit_zero ha
    set gbar : IsLocalRing.ResidueField A₀ →+* (↥(chartAlgFin A F j) ⧸ y) := IsLocalRing.ResidueField.lift f with hgbar
    letI instAlgκ : Algebra (IsLocalRing.ResidueField A₀) (↥(chartAlgFin A F j) ⧸ y) := gbar.toAlgebra

    set jbar : ↥(chartAlgFin A F j) ⧸ y := Ideal.Quotient.mk y (c (jChartFin A₀ F₀ j₀)) with hjbar
    have hφCjbar : φC (jChartFin A F j) = algebraMap (↥(chartAlgFin A F j) ⧸ y) (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y)) jbar := by
      rw [hφC, ← hcj, RingHom.comp_apply]
    have hjalg : IsAlgebraic (IsLocalRing.ResidueField A₀) jbar := by
      set k' := algebraicClosure (IsLocalRing.ResidueField A₀) (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y)) with hk'
      haveI : IsAlgClosed ↥k' := IsAlgClosure.isAlgClosed (IsLocalRing.ResidueField A₀)
      have h925 := ModularCurve.ssJSet_eq_image_algebraMap_of_isAlgClosed q (↥k') (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y))
      have hmem : φC (jChartFin A F j) ∈ algebraMap (↥k') (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y)) ''
          @ModularCurve.ssJSet q (↥k') _ (Classical.decEq _) := by
        rw [← h925]
        convert hφCj
      obtain ⟨t, -, ht⟩ := hmem
      have htalg : IsAlgebraic (IsLocalRing.ResidueField A₀) ((t : ↥k') : AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y)) :=
        mem_algebraicClosure_iff.mp t.2
      rw [hφCjbar] at ht
      have : IsAlgebraic (IsLocalRing.ResidueField A₀)
          ((IsScalarTower.toAlgHom (IsLocalRing.ResidueField A₀) (↥(chartAlgFin A F j) ⧸ y) (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y))) jbar) := by
        rw [IsScalarTower.coe_toAlgHom', ← ht]
        exact htalg
      exact (isAlgebraic_algHom_iff _
        (algebraMap (↥(chartAlgFin A F j) ⧸ y) (AlgebraicClosure (↥(chartAlgFin A F j) ⧸ y))).injective).mp this
    have hjint : IsIntegral (IsLocalRing.ResidueField A₀) jbar := hjalg.isIntegral

    haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A₀)
        ↥(Algebra.adjoin (IsLocalRing.ResidueField A₀) ({jbar} : Set (↥(chartAlgFin A F j) ⧸ y))) :=
      Algebra.IsIntegral.adjoin (fun x hx => by rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hjint)
    have hfield : IsField ↥(Algebra.adjoin (IsLocalRing.ResidueField A₀) ({jbar} : Set (↥(chartAlgFin A F j) ⧸ y))) :=
      isField_of_isIntegral_of_isField' (R := IsLocalRing.ResidueField A₀) (Field.toIsField (IsLocalRing.ResidueField A₀))

    set g : Polynomial A₀ →+* (↥(chartAlgFin A F j) ⧸ y) := (Ideal.Quotient.mk y).comp (c.comp θ) with hg
    have hgeq : g = (Polynomial.aeval jbar : Polynomial (IsLocalRing.ResidueField A₀) →ₐ[_] (↥(chartAlgFin A F j) ⧸ y)).toRingHom.comp
        (Polynomial.mapRingHom (IsLocalRing.residue A₀)) := by
      apply Polynomial.ringHom_ext
      · intro a
        rw [hg, RingHom.comp_apply, RingHom.comp_apply, hθC, RingHom.comp_apply, Polynomial.coe_mapRingHom,
          Polynomial.map_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C]
        show f a = gbar (IsLocalRing.residue A₀ a)
        rw [hgbar, IsLocalRing.ResidueField.lift_residue_apply]
      · rw [hg, RingHom.comp_apply, RingHom.comp_apply, hθX, RingHom.comp_apply, Polynomial.coe_mapRingHom,
          Polynomial.map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
    have hrange : g.range = (Algebra.adjoin (IsLocalRing.ResidueField A₀) ({jbar} : Set (↥(chartAlgFin A F j) ⧸ y))).toSubring := by
      ext z
      rw [RingHom.mem_range, Subalgebra.mem_toSubring, Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
      constructor
      · rintro ⟨P, rfl⟩
        refine ⟨P.map (IsLocalRing.residue A₀), ?_⟩
        rw [hgeq]
        rfl
      · rintro ⟨p, rfl⟩
        obtain ⟨P, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue A₀) IsLocalRing.residue_surjective p
        refine ⟨P, ?_⟩
        rw [hgeq]
        rfl
    have hqfield : IsField (Polynomial A₀ ⧸ RingHom.ker g) :=
      MulEquiv.isField hfield
        ((RingHom.quotientKerEquivRange g).trans (RingEquiv.subringCongr hrange)).toMulEquiv
    have hPmax : (RingHom.ker g).IsMaximal := Ideal.Quotient.maximal_of_isField _ hqfield
    have hker : RingHom.ker g = (Ideal.comap c y).comap θ := by
      rw [hg, ← RingHom.comap_ker, Ideal.mk_ker, ← Ideal.comap_comap]
    rw [hker] at hPmax
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' θ hθint (Ideal.comap c y) hPmax
  exact ⟨hi, hii, hiii⟩

end S_AlgebraicCurve_TwoChartIntegralModel_isMaximal_comap_and_mem_comap_and_mem_ssJSet_of_ringHom_chartAlgFin
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isMaximal_comap_and_mem_comap_and_mem_ssJSet_of_ringHom_chartAlgFin (solution)
