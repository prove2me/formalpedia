-- Prove2me | solution 1 for AlgebraicCurve.Place.derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/24bfeedc-e1ea-517b-8729-8af8c7b04e1b

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne.AlgebraicCurve Polynomial IsLocalRing"
open scoped Polynomial.Bivariate

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place finiteDimensional_adjoin_of_transcendental"
namespace Place
p2m_export "AlgebraicCurve.Place" "ord_neg mem_maximalIdeal_iff_ord_pos fiberOver mem_fiberOver restrict_mem_fiberOver ramificationIndex ramificationIndex_le_ord ramificationIndex_pos restrict mem_restrict_iff ord_restrict inertiaDeg deg_restrict_mul_inertiaDeg ext coe_algebraMap ResidueField deg ord ord_zero ord_mul ord_coe_unit ord_zpow algebraMap_mem' toValuationSubring isUnit_mk_of_ord_eq_zero evalAt_algebraMap_eq deg_eq_one_of_isRational IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt ord_nonneg_of_mem ord_norm_eq_sum_fiberOver mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem g2p_algebraMap_comp :
    (algebraMap v.toValuationSubring F).comp (algebraMap K v.toValuationSubring) = algebraMap K F :=
  (IsScalarTower.algebraMap_eq K v.toValuationSubring F).symm

private theorem _root_.AlgebraicCurve.Place.g2p_hom_evalEval {S : Type*} [CommRing S] (φ : v.toValuationSubring →+* S)
    (P : K[X][Y]) (a b : v.toValuationSubring) :
    φ ((P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval a b)
      = (P.map (mapRingHom (φ.comp (algebraMap K v.toValuationSubring)))).evalEval (φ a) (φ b) := by
  rw [← map_mapRingHom_evalEval φ, Polynomial.map_map, mapRingHom_comp]

p2m_export "AlgebraicCurve.Place" "g2p_hom_evalEval"
private theorem _root_.AlgebraicCurve.Place.g2p_hom_eval {S : Type*} [CommRing S] (φ : v.toValuationSubring →+* S)
    (p : K[X]) (a : v.toValuationSubring) :
    φ ((p.map (algebraMap K v.toValuationSubring)).eval a)
      = (p.map (φ.comp (algebraMap K v.toValuationSubring))).eval (φ a) := by
  rw [eval_map, eval_map, hom_eval₂]

p2m_export "AlgebraicCurve.Place" "g2p_hom_eval"
private theorem _root_.AlgebraicCurve.Place.g2p_coe_evalEval (P : K[X][Y]) (a b : v.toValuationSubring) :
    (((P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval a b : v.toValuationSubring) : F)
      = (P.map (mapRingHom (algebraMap K F))).evalEval (a : F) (b : F) := by
  have h := v.g2p_hom_evalEval (algebraMap v.toValuationSubring F) P a b
  rw [g2p_algebraMap_comp] at h
  exact h

p2m_export "AlgebraicCurve.Place" "g2p_coe_evalEval"
private theorem _root_.AlgebraicCurve.Place.g2p_coe_eval (p : K[X]) (a : v.toValuationSubring) :
    (((p.map (algebraMap K v.toValuationSubring)).eval a : v.toValuationSubring) : F)
      = (p.map (algebraMap K F)).eval (a : F) := by
  have h := v.g2p_hom_eval (algebraMap v.toValuationSubring F) p a
  rw [g2p_algebraMap_comp] at h
  exact h

p2m_export "AlgebraicCurve.Place" "g2p_coe_eval"
private theorem _root_.AlgebraicCurve.Place.g2p_evalEval_mem (P : K[X][Y]) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring) :
    (P.map (mapRingHom (algebraMap K F))).evalEval z y ∈ v.toValuationSubring := by
  rw [← v.g2p_coe_evalEval P ⟨z, hz⟩ ⟨y, hy⟩]
  exact SetLike.coe_mem _

p2m_export "AlgebraicCurve.Place" "g2p_evalEval_mem"
private theorem _root_.AlgebraicCurve.Place.g2p_eval_mem (p : K[X]) {z : F} (hz : z ∈ v.toValuationSubring) :
    (p.map (algebraMap K F)).eval z ∈ v.toValuationSubring := by
  rw [← v.g2p_coe_eval p ⟨z, hz⟩]
  exact SetLike.coe_mem _

p2m_export "AlgebraicCurve.Place" "g2p_eval_mem"

theorem g2p_algebraMap_residueField (c : K) :
    algebraMap K v.ResidueField c
      = residue v.toValuationSubring (algebraMap K v.toValuationSubring c) := by
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c,
    ResidueField.algebraMap_eq]

private theorem _root_.AlgebraicCurve.Place.g2p_residue_mk (hv : v.IsRational) (a : v.toValuationSubring) :
    residue v.toValuationSubring a = algebraMap K v.ResidueField (v.evalAt (a : F)) := by
  rw [v.algebraMap_evalAt hv a.2]

p2m_export "AlgebraicCurve.Place" "g2p_residue_mk"

private theorem _root_.AlgebraicCurve.Place.g2p_evalAt_evalEval (hv : v.IsRational) (P : K[X][Y]) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring) :
    v.evalAt ((P.map (mapRingHom (algebraMap K F))).evalEval z y)
      = P.evalEval (v.evalAt z) (v.evalAt y) := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (v.g2p_evalEval_mem P hz hy)]
  have hmk : (⟨(P.map (mapRingHom (algebraMap K F))).evalEval z y, v.g2p_evalEval_mem P hz hy⟩
        : v.toValuationSubring)
      = (P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval ⟨z, hz⟩ ⟨y, hy⟩ :=
    Subtype.ext (by rw [g2p_coe_evalEval])
  rw [hmk, ← ResidueField.algebraMap_eq, g2p_hom_evalEval,
    ← IsScalarTower.algebraMap_eq K v.toValuationSubring v.ResidueField,
    ResidueField.algebraMap_eq, v.g2p_residue_mk hv, v.g2p_residue_mk hv,
    map_mapRingHom_evalEval]

p2m_export "AlgebraicCurve.Place" "g2p_evalAt_evalEval"
private theorem _root_.AlgebraicCurve.Place.g2p_evalAt_eval (hv : v.IsRational) (p : K[X]) {z : F} (hz : z ∈ v.toValuationSubring) :
    v.evalAt ((p.map (algebraMap K F)).eval z) = p.eval (v.evalAt z) := by
  have h := v.g2p_evalAt_evalEval hv (C p) hz hz
  rwa [Polynomial.map_C, evalEval_C, evalEval_C] at h

p2m_export "AlgebraicCurve.Place" "g2p_evalAt_eval"

private theorem _root_.AlgebraicCurve.Place.g2p_sub_mem_maximalIdeal (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    (⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) : v.toValuationSubring)
      ∈ maximalIdeal v.toValuationSubring := by
  rw [← residue_eq_zero_iff, map_sub, ← g2p_algebraMap_residueField, v.g2p_residue_mk hv, sub_self]

p2m_export "AlgebraicCurve.Place" "g2p_sub_mem_maximalIdeal"

theorem g2p_isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have hab : a + b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have ha' : a ∈ maximalIdeal R := by simpa using sub_mem hab hb
  exact (IsLocalRing.mem_maximalIdeal _).mp ha' ha

end AlgebraicCurve.Place

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne.AlgebraicCurve Polynomial Polynomial.Bivariate.Polynomial IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place finiteDimensional_adjoin_of_transcendental"
namespace Place
p2m_export "AlgebraicCurve.Place" "ord_neg mem_maximalIdeal_iff_ord_pos fiberOver mem_fiberOver restrict_mem_fiberOver ramificationIndex ramificationIndex_le_ord ramificationIndex_pos restrict mem_restrict_iff ord_restrict inertiaDeg deg_restrict_mul_inertiaDeg ext coe_algebraMap ResidueField deg ord ord_zero ord_mul ord_coe_unit ord_zpow algebraMap_mem' toValuationSubring isUnit_mk_of_ord_eq_zero evalAt_algebraMap_eq deg_eq_one_of_isRational IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt ord_nonneg_of_mem ord_norm_eq_sum_fiberOver mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section absolute
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.rfg_evalAt_sub_algebraMap (hv : v.IsRational) {y : F} (hy : y ∈ v.toValuationSubring) (c : K) :
    v.evalAt (y - algebraMap K F c) = v.evalAt y - c := by
  have h := v.g2p_evalAt_eval hv (X - C c) hy
  simpa [Polynomial.map_sub] using h

p2m_export "AlgebraicCurve.Place" "rfg_evalAt_sub_algebraMap"

private theorem _root_.AlgebraicCurve.Place.rfg_ord_sub_algebraMap_eq_zero_of_evalAt_ne (hv : v.IsRational) {y : F}
    (hy : y ∈ v.toValuationSubring) {c : K} (hc : v.evalAt y ≠ c) :
    v.ord (y - algebraMap K F c) = 0 := by
  have hmem : y - algebraMap K F c ∈ v.toValuationSubring := sub_mem hy (v.algebraMap_mem' c)
  have hval : v.evalAt (y - algebraMap K F c) ≠ 0 := by
    rw [v.rfg_evalAt_sub_algebraMap hv hy]
    exact sub_ne_zero.mpr hc
  have hunit : IsUnit (⟨y - algebraMap K F c, hmem⟩ : v.toValuationSubring) := by
    rw [← residue_ne_zero_iff_isUnit, v.g2p_residue_mk hv]
    exact (_root_.map_ne_zero _).mpr hval
  exact v.ord_coe_unit hunit.unit

p2m_export "AlgebraicCurve.Place" "rfg_ord_sub_algebraMap_eq_zero_of_evalAt_ne"

private theorem _root_.AlgebraicCurve.Place.rfg_ord_sub_algebraMap_pos (hv : v.IsRational) {y : F}
    (hy : y ∈ v.toValuationSubring) {c : K} (h : v.evalAt y = c) (h0 : y ≠ algebraMap K F c) :
    0 < v.ord (y - algebraMap K F c) := by
  have hmem : y - algebraMap K F c ∈ v.toValuationSubring := sub_mem hy (v.algebraMap_mem' c)
  have hmax : (⟨y - algebraMap K F c, hmem⟩ : v.toValuationSubring)
      ∈ maximalIdeal v.toValuationSubring := by
    have := v.g2p_sub_mem_maximalIdeal hv hy
    rw [h] at this
    convert this using 1
    rfl
  exact (v.mem_maximalIdeal_iff_ord_pos (sub_ne_zero.mpr h0) hmem).mp hmax

p2m_export "AlgebraicCurve.Place" "rfg_ord_sub_algebraMap_pos"
end absolute

section tower
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F']

private theorem _root_.AlgebraicCurve.Place.rfg_ramificationIndex_eq_one_of_ord_eq_one [Algebra.IsIntegral F F'] (w : Place K F')
    {t : F} (ht : w.ord (algebraMap F F' t) = 1) : w.ramificationIndex F = 1 := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, map_zero, ord_zero] at ht
    exact zero_ne_one ht
  have h1 := w.ramificationIndex_le_ord (F := F) ht0 (by rw [ht]; exact one_pos)
  have h2 := w.ramificationIndex_pos (F := F)
  rw [ht] at h1
  omega

p2m_export "AlgebraicCurve.Place" "rfg_ramificationIndex_eq_one_of_ord_eq_one"

private theorem _root_.AlgebraicCurve.Place.rfg_inertiaDeg_eq_one_of_isRational [Algebra.IsIntegral F F'] (w : Place K F')
    (hw : w.IsRational) : w.inertiaDeg F = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [deg_eq_one_of_isRational hw] at h
  exact Nat.eq_one_of_mul_eq_one_left h

p2m_export "AlgebraicCurve.Place" "rfg_inertiaDeg_eq_one_of_isRational"
end tower

end AlgebraicCurve.Place

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne.AlgebraicCurve Polynomial Polynomial.Bivariate.Polynomial IsLocalRing"
p2m_open_scoped "Polynomial.Bivariate Polynomial.Bivariate.Polynomial.Bivariate"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place finiteDimensional_adjoin_of_transcendental"
namespace Place
p2m_export "AlgebraicCurve.Place" "ord_neg mem_maximalIdeal_iff_ord_pos fiberOver mem_fiberOver restrict_mem_fiberOver ramificationIndex ramificationIndex_le_ord ramificationIndex_pos restrict mem_restrict_iff ord_restrict inertiaDeg deg_restrict_mul_inertiaDeg ext coe_algebraMap ResidueField deg ord ord_zero ord_mul ord_coe_unit ord_zpow algebraMap_mem' toValuationSubring isUnit_mk_of_ord_eq_zero evalAt_algebraMap_eq deg_eq_one_of_isRational IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt ord_nonneg_of_mem ord_norm_eq_sum_fiberOver mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

theorem rf_local {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Q : Place K F) (hv : Q.IsRational) {z y : F}
    (hzQ : z ∈ Q.toValuationSubring) (hyQ : y ∈ Q.toValuationSubring)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hyne : y - algebraMap K F (Q.evalAt y) ≠ 0)
    (m : ℕ) (hm1 : 1 ≤ m)
    (hcount : (m : ℤ) * Q.ord ((G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z
        (algebraMap K F (Q.evalAt y))) = Q.ord (y - algebraMap K F (Q.evalAt y))) :
    (Polynomial.derivative G).evalEval (Q.evalAt z) (Q.evalAt y) ≠ 0 := by
  have ha1 : 1 ≤ Q.ord (y - algebraMap K F (Q.evalAt y)) := by
    have := Q.rfg_ord_sub_algebraMap_pos hv hyQ rfl (fun h => hyne (sub_eq_zero.mpr h))
    omega
  set zO : Q.toValuationSubring := ⟨z, hzQ⟩ with hzO
  set yO : Q.toValuationSubring := ⟨y, hyQ⟩ with hyO
  set y0 : Q.toValuationSubring := algebraMap K Q.toValuationSubring (Q.evalAt y) with hy0
  set GO : (Q.toValuationSubring)[X][Y] := G.map (mapRingHom (algebraMap K Q.toValuationSubring)) with hGO
  set pQ : (Q.toValuationSubring)[X] := GO.map (evalRingHom zO) with hpQ
  have hpev : ∀ t, pQ.eval t = GO.evalEval zO t := fun t => map_evalRingHom_eval zO t GO
  have h1 : pQ.eval yO = 0 := by
    rw [hpev, ← ZeroMemClass.coe_eq_zero, hGO, g2p_coe_evalEval]
    exact hG

  have hcoe0 : ((pQ.eval y0 : Q.toValuationSubring) : F)
      = (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z (algebraMap K F (Q.evalAt y)) := by
    rw [hpev, hGO, g2p_coe_evalEval, hy0, Q.coe_algebraMap]

  obtain ⟨k, hk⟩ := binomExpansion pQ y0 (yO - y0)
  rw [add_sub_cancel, h1] at hk
  set u : Q.toValuationSubring := pQ.derivative.eval y0 + k * (yO - y0) with hu
  have hTaylor : pQ.eval y0 = -((yO - y0) * u) := by
    rw [hu]
    linear_combination -hk

  have hpQ0 : pQ.eval y0 ≠ 0 := by
    intro h0
    have : Q.ord ((pQ.eval y0 : Q.toValuationSubring) : F) = 0 := by rw [h0]; simp
    rw [← hcoe0, this, mul_zero] at hcount
    omega
  have hu0 : u ≠ 0 := by
    intro h0
    apply hpQ0
    rw [hTaylor, h0, mul_zero, neg_zero]
  have hu0' : ((u : Q.toValuationSubring) : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hu0
  have hordu : 0 ≤ Q.ord ((u : Q.toValuationSubring) : F) := Q.ord_nonneg_of_mem u.2
  have hsub0 : ((yO : Q.toValuationSubring) : F) - (y0 : F) ≠ 0 := by
    simpa [hyO, hy0, Q.coe_algebraMap] using hyne
  have hord_split : Q.ord ((pQ.eval y0 : Q.toValuationSubring) : F)
      = Q.ord (y - algebraMap K F (Q.evalAt y)) + Q.ord ((u : Q.toValuationSubring) : F) := by
    rw [hTaylor]
    push_cast
    rw [ord_neg, Q.ord_mul hsub0 hu0']
    simp [hyO, hy0, Q.coe_algebraMap]

  have hordu0 : Q.ord ((u : Q.toValuationSubring) : F) = 0 := by
    have h := hcount
    rw [← hcoe0, hord_split] at h
    nlinarith

  have huunit : IsUnit u := by
    have := Q.isUnit_mk_of_ord_eq_zero hu0' hordu0
    convert this using 1
  have hderunit : IsUnit (pQ.derivative.eval y0) := by
    have hsplit : pQ.derivative.eval y0 = u + (-(k * (yO - y0))) := by rw [hu]; ring
    rw [hsplit]
    refine g2p_isUnit_add_of_mem_maximalIdeal huunit (Submodule.neg_mem _ ?_)
    exact Ideal.mul_mem_left _ _ (by simpa [hyO, hy0] using Q.g2p_sub_mem_maximalIdeal hv hyQ)
  have hder_coe : ((pQ.derivative.eval y0 : Q.toValuationSubring) : F)
      = ((Polynomial.derivative G).map (mapRingHom (algebraMap K F))).evalEval z
          (algebraMap K F (Q.evalAt y)) := by
    rw [hpQ, derivative_map, map_evalRingHom_eval, hGO, derivative_map, g2p_coe_evalEval, hy0, Q.coe_algebraMap]
  have hval : Q.evalAt ((pQ.derivative.eval y0 : Q.toValuationSubring) : F)
      = (Polynomial.derivative G).evalEval (Q.evalAt z) (Q.evalAt y) := by
    rw [hder_coe, Q.g2p_evalAt_evalEval hv _ hzQ (Q.algebraMap_mem' _), Q.evalAt_algebraMap_eq]
  rw [← hval]
  intro h0
  have hres := Q.g2p_residue_mk hv (pQ.derivative.eval y0)
  rw [h0, map_zero, residue_eq_zero_iff] at hres
  exact (IsLocalRing.mem_maximalIdeal _).mp hres hderunit

theorem rf_degenerate {K F₀ F : Type*} [Field K] [Field F₀] [Field F]
    [Algebra K F₀] [Algebra K F] [Algebra F₀ F] [IsScalarTower K F₀ F]
    (zz : F₀) (hzz : Transcendental K zz) (y : F)
    (G : Polynomial (Polynomial K)) (hGirr : Irreducible G)
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval (algebraMap F₀ F zz) y = 0)
    (Q : Place K F) (hyc : y = algebraMap K F (Q.evalAt y)) :
    (Polynomial.derivative G).evalEval (Q.evalAt (algebraMap F₀ F zz)) (Q.evalAt y) ≠ 0 := by
  set p : K[X] := G.eval (C (Q.evalAt y)) with hp

  have hev : (G.map (mapRingHom (algebraMap K F))).eval (C y) = p.map (algebraMap K F) := by
    rw [hyc, hp, ← Polynomial.map_C (algebraMap K F), map_mapRingHom_eval_map]
  have hpF : (p.map (algebraMap K F)).eval (algebraMap F₀ F zz) = 0 := by
    have h2 := hG
    unfold Polynomial.evalEval at h2
    rwa [hev] at h2

  have hp0 : p = 0 := by
    have h3 : algebraMap F₀ F ((p.map (algebraMap K F₀)).eval zz) = 0 := by
      rw [eval_map, hom_eval₂, ← IsScalarTower.algebraMap_eq, ← eval_map]
      exact hpF
    have h4 : Polynomial.aeval zz p = 0 := by
      rw [Polynomial.aeval_def, ← eval_map]
      exact (map_eq_zero_iff _ (algebraMap F₀ F).injective).mp h3
    exact transcendental_iff_injective.mp hzz (by rw [h4, map_zero])

  have hdvd : (X - C (C (Q.evalAt y))) ∣ G := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hp0
  obtain ⟨H, hH⟩ := hdvd
  have hXu : ¬ IsUnit (X - C (C (Q.evalAt y)) : K[X][Y]) := fun hu => by
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_sub_C] at this
    exact one_ne_zero this
  have hHu : IsUnit H := (hGirr.isUnit_or_isUnit hH).resolve_left hXu
  obtain ⟨r, hr, hrH⟩ := Polynomial.isUnit_iff.mp hHu
  obtain ⟨u, hu, hur⟩ := Polynomial.isUnit_iff.mp hr
  have hder : Polynomial.derivative G = C (C u) := by
    rw [hH, ← hrH, ← hur, derivative_mul]
    simp
  rw [hder, evalEval_C, eval_C]
  exact hu.ne_zero

section tower
variable {K F₀ F : Type*} [Field K] [Field F₀] [Field F]
  [Algebra K F₀] [Algebra K F] [Algebra F₀ F] [IsScalarTower K F₀ F]

theorem rf_fibre_value [FiniteDimensional F₀ F] [Algebra.IsSeparable F₀ F]
    (zz : F₀) (Q : Place K F) (hzQ : algebraMap F₀ F zz ∈ Q.toValuationSubring)
    (he : Q.ord (algebraMap F₀ F zz - algebraMap K F (Q.evalAt (algebraMap F₀ F zz))) = 1)
    {w : Place K F} (hwrat : w.IsRational) (hw : w ∈ (Q.restrict F₀).fiberOver F) :
    algebraMap F₀ F zz ∈ w.toValuationSubring ∧
      w.evalAt (algebraMap F₀ F zz) = Q.evalAt (algebraMap F₀ F zz) := by

  have hwr : w.restrict F₀ = Q.restrict F₀ := (mem_fiberOver _).mp hw
  have hzw : algebraMap F₀ F zz ∈ w.toValuationSubring := by
    have h : zz ∈ (w.restrict F₀).toValuationSubring := by
      rw [hwr]
      exact (Q.mem_restrict_iff).mpr hzQ
    exact (w.mem_restrict_iff).mp h
  refine ⟨hzw, ?_⟩

  set z₀ : K := Q.evalAt (algebraMap F₀ F zz) with hz₀
  set t : F₀ := zz - algebraMap K F₀ z₀ with ht
  have htF : algebraMap F₀ F t = algebraMap F₀ F zz - algebraMap K F z₀ := by
    rw [ht, map_sub, ← IsScalarTower.algebraMap_apply]
  have hQt : Q.ord (algebraMap F₀ F t) = 1 := by rw [htF]; exact he
  have heQ : Q.ramificationIndex F₀ = 1 := Q.rfg_ramificationIndex_eq_one_of_ord_eq_one hQt
  have hvt : (Q.restrict F₀).ord t = 1 := by
    have h := Q.ord_restrict (F := F₀) t
    rw [hQt, heQ, Nat.cast_one, one_mul] at h
    exact h.symm
  have hwt : 0 < w.ord (algebraMap F₀ F zz - algebraMap K F z₀) := by
    rw [← htF, w.ord_restrict (F := F₀) t, hwr, hvt, mul_one]
    exact_mod_cast w.ramificationIndex_pos (F := F₀)

  by_contra hne
  have h0 := w.rfg_ord_sub_algebraMap_eq_zero_of_evalAt_ne hwrat hzw hne
  rw [h0] at hwt
  exact lt_irrefl _ hwt

theorem rf_norm_count [CharZero F₀] [FiniteDimensional F₀ F] [Algebra.IsSeparable F₀ F]
    (y : F) (Q : Place K F) (hQ : Q.IsRational)
    (hyne : y - algebraMap K F (Q.evalAt y) ≠ 0)
    (hfib : ∀ w ∈ (Q.restrict F₀).fiberOver F, w ≠ Q → w.ord (y - algebraMap K F (Q.evalAt y)) = 0) :
    ((Module.finrank F₀ F / (minpoly F₀ y).natDegree : ℕ) : ℤ)
        * (Q.restrict F₀).ord ((minpoly F₀ y).eval (algebraMap K F₀ (Q.evalAt y)))
      = Q.ord (y - algebraMap K F (Q.evalAt y)) := by
  set c : F₀ := algebraMap K F₀ (Q.evalAt y) with hc
  have hcF : algebraMap F₀ F c = algebraMap K F (Q.evalAt y) := by
    rw [hc, ← IsScalarTower.algebraMap_apply]
  have hne' : algebraMap F₀ F c - y ≠ 0 := by
    rw [hcF]
    intro h
    exact hyne (by rw [← neg_sub, h, neg_zero])
  have hnorm : (Q.restrict F₀).ord (Algebra.norm F₀ (algebraMap F₀ F c - y))
      = Q.ord (y - algebraMap K F (Q.evalAt y)) := by
    rw [(Q.restrict F₀).ord_norm_eq_sum_fiberOver hne', Finset.sum_eq_single Q]
    · rw [Q.rfg_inertiaDeg_eq_one_of_isRational (F := F₀) hQ, hcF, ← neg_sub, ord_neg]
      simp
    · intro w hw hwQ
      rw [hcF, ← neg_sub, ord_neg, hfib w hw hwQ, mul_zero]
    · intro hQ'
      exact absurd (restrict_mem_fiberOver (F := F₀) Q) hQ'
  rw [← hnorm, Algebra.norm_algebraMap_sub_eq_eval_minpoly_pow y c, ← zpow_natCast, ord_zpow]

theorem rf_ord_specialisation [FiniteDimensional F₀ F]
    (zz : F₀) (y : F) (G : Polynomial (Polynomial K))
    (ℓ : F₀) (hℓ : algebraMap F₀ F ℓ = ((G.leadingCoeff).map (algebraMap K F)).eval (algebraMap F₀ F zz))
    (hS4 : ∀ c : F₀,
      ((G.map (Polynomial.mapRingHom (algebraMap K F₀))).map (evalRingHom zz)).eval c
        = ℓ * (minpoly F₀ y).eval c)
    (Q : Place K F) (hQ : Q.IsRational) (hzQ : algebraMap F₀ F zz ∈ Q.toValuationSubring)
    (heQ : Q.ramificationIndex F₀ = 1)
    (hlead : G.leadingCoeff.eval (Q.evalAt (algebraMap F₀ F zz)) ≠ 0) :
    Q.ord ((G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval (algebraMap F₀ F zz)
        (algebraMap K F (Q.evalAt y)))
      = (Q.restrict F₀).ord ((minpoly F₀ y).eval (algebraMap K F₀ (Q.evalAt y))) := by

  have hmem : ((G.leadingCoeff).map (algebraMap K F)).eval (algebraMap F₀ F zz) ∈ Q.toValuationSubring :=
    Q.g2p_eval_mem _ hzQ
  have hval : Q.evalAt (((G.leadingCoeff).map (algebraMap K F)).eval (algebraMap F₀ F zz)) ≠ 0 := by
    rw [Q.g2p_evalAt_eval hQ _ hzQ]
    exact hlead
  have hunit : IsUnit (⟨((G.leadingCoeff).map (algebraMap K F)).eval (algebraMap F₀ F zz), hmem⟩
      : Q.toValuationSubring) := by
    rw [← residue_ne_zero_iff_isUnit, Q.g2p_residue_mk hQ]
    exact (_root_.map_ne_zero _).mpr hval
  have hordℓF : Q.ord (algebraMap F₀ F ℓ) = 0 := by
    rw [hℓ]
    exact Q.ord_coe_unit hunit.unit
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    apply hunit.ne_zero
    ext
    show ((G.leadingCoeff).map (algebraMap K F)).eval (algebraMap F₀ F zz) = ((0 : Q.toValuationSubring) : F)
    rw [← hℓ, map_zero]
    simp
  have hordℓ : (Q.restrict F₀).ord ℓ = 0 := by
    have h := Q.ord_restrict (F := F₀) ℓ
    rw [hordℓF, heQ, Nat.cast_one, one_mul] at h
    exact h.symm

  have hkey : algebraMap F₀ F
        (((G.map (Polynomial.mapRingHom (algebraMap K F₀))).map (evalRingHom zz)).eval
          (algebraMap K F₀ (Q.evalAt y)))
      = (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval (algebraMap F₀ F zz)
          (algebraMap K F (Q.evalAt y)) := by
    rw [map_evalRingHom_eval, ← map_mapRingHom_evalEval (algebraMap F₀ F), Polynomial.map_map,
      mapRingHom_comp, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [← hkey, Q.ord_restrict (F := F₀), heQ, Nat.cast_one, one_mul, hS4]

  by_cases hm : (minpoly F₀ y).eval (algebraMap K F₀ (Q.evalAt y)) = 0
  · rw [hm, mul_zero]
  · rw [(Q.restrict F₀).ord_mul hℓ0 hm, hordℓ, zero_add]

theorem rf_tower [CharZero F₀] [FiniteDimensional F₀ F] [Algebra.IsSeparable F₀ F]
    (hrat : ∀ w : Place K F, w.IsRational)
    (zz : F₀) (hzz : Transcendental K zz) (y : F)
    (G : Polynomial (Polynomial K)) (hGirr : Irreducible G)
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval (algebraMap F₀ F zz) y = 0)
    (ℓ : F₀) (hℓ : algebraMap F₀ F ℓ = ((G.leadingCoeff).map (algebraMap K F)).eval (algebraMap F₀ F zz))
    (hS4 : ∀ c : F₀,
      ((G.map (Polynomial.mapRingHom (algebraMap K F₀))).map (evalRingHom zz)).eval c
        = ℓ * (minpoly F₀ y).eval c)
    (Q : Place K F) (hzQ : algebraMap F₀ F zz ∈ Q.toValuationSubring) (hyQ : y ∈ Q.toValuationSubring)
    (he : Q.ord (algebraMap F₀ F zz - algebraMap K F (Q.evalAt (algebraMap F₀ F zz))) = 1)
    (hlead : G.leadingCoeff.eval (Q.evalAt (algebraMap F₀ F zz)) ≠ 0)
    (hsep : ∀ Q' : Place K F, Q' ≠ Q → algebraMap F₀ F zz ∈ Q'.toValuationSubring →
      Q'.evalAt (algebraMap F₀ F zz) = Q.evalAt (algebraMap F₀ F zz) →
      y ∈ Q'.toValuationSubring → Q'.evalAt y ≠ Q.evalAt y) :
    (Polynomial.derivative G).evalEval (Q.evalAt (algebraMap F₀ F zz)) (Q.evalAt y) ≠ 0 := by
  have hv := hrat Q

  by_cases hyc : y = algebraMap K F (Q.evalAt y)
  · exact rf_degenerate zz hzz y G hGirr hG Q hyc
  have hyne : y - algebraMap K F (Q.evalAt y) ≠ 0 := fun h => hyc (sub_eq_zero.mp h)
  have heQ : Q.ramificationIndex F₀ = 1 := by
    refine Q.rfg_ramificationIndex_eq_one_of_ord_eq_one (t := zz - algebraMap K F₀ (Q.evalAt (algebraMap F₀ F zz))) ?_
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
    exact he

  have hfib : ∀ w ∈ (Q.restrict F₀).fiberOver F, w ≠ Q → w.ord (y - algebraMap K F (Q.evalAt y)) = 0 := by
    intro w hw hwQ
    obtain ⟨hwz, hwz₀⟩ := rf_fibre_value zz Q hzQ he (hrat w) hw
    have hwy : y ∈ w.toValuationSubring :=
      w.mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero (hrat w) hwz G hG
        (by rw [hwz₀]; exact hlead)
    exact w.rfg_ord_sub_algebraMap_eq_zero_of_evalAt_ne (hrat w) hwy (hsep w hwQ hwz hwz₀ hwy)

  have hcount := rf_norm_count (F₀ := F₀) y Q hv hyne hfib
  rw [← rf_ord_specialisation zz y G ℓ hℓ hS4 Q hv hzQ heQ hlead] at hcount

  have hyint : IsIntegral F₀ y := Algebra.IsIntegral.isIntegral y
  exact rf_local Q hv hzQ hyQ G hG hyne _
    (Nat.div_pos (minpoly.natDegree_le y) (minpoly.natDegree_pos hyint)) hcount

end tower

theorem rf_gauss_minpoly {K F : Type*} [Field K] [Field F] [Algebra K F]
    {z : F} (hz : Transcendental K z) (y : F)
    [FiniteDimensional (IntermediateField.adjoin K ({z} : Set F)) F]
    (G : Polynomial (Polynomial K)) (hGirr : Irreducible G)
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (c : IntermediateField.adjoin K ({z} : Set F)) :
    ((G.map (Polynomial.mapRingHom (algebraMap K (IntermediateField.adjoin K ({z} : Set F))))).map
        (evalRingHom (⟨z, IntermediateField.mem_adjoin_simple_self K z⟩ :
          IntermediateField.adjoin K ({z} : Set F)))).eval c
      = ((G.leadingCoeff).map (algebraMap K (IntermediateField.adjoin K ({z} : Set F)))).eval
            ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
        * (minpoly (IntermediateField.adjoin K ({z} : Set F)) y).eval c := by

  set zz : IntermediateField.adjoin K ({z} : Set F) :=
    ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩ with hzzdef
  have hzzF : algebraMap (IntermediateField.adjoin K ({z} : Set F)) F zz = z := rfl
  set φ : K[X] →+* IntermediateField.adjoin K ({z} : Set F) :=
    (evalRingHom zz).comp (mapRingHom (algebraMap K (IntermediateField.adjoin K ({z} : Set F))))
    with hφdef
  have hφapply : ∀ p : K[X], φ p = aeval zz p := by
    intro p
    simp only [hφdef, RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, coe_evalRingHom,
      eval_map_algebraMap]

  have hψ : ∀ p : K[X], RatFunc.algEquivOfTranscendental z hz (algebraMap K[X] (RatFunc K) p) = φ p := by
    intro p
    rw [RatFunc.algEquivOfTranscendental_algebraMap, hφapply]
    rfl
  have hφinj : Function.Injective φ := by
    intro p q hpq
    rw [← hψ, ← hψ] at hpq
    exact IsFractionRing.injective K[X] (RatFunc K)
      ((RatFunc.algEquivOfTranscendental z hz).injective hpq)

  have hGz : (G.map (mapRingHom (algebraMap K (IntermediateField.adjoin K ({z} : Set F))))).map
      (evalRingHom zz) = G.map φ := Polynomial.map_map _ _ _

  have hφF : (algebraMap (IntermediateField.adjoin K ({z} : Set F)) F).comp φ
      = (evalRingHom z).comp (mapRingHom (algebraMap K F)) := by
    refine Polynomial.ringHom_ext (fun k => ?_) ?_
    · simp only [RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, Polynomial.map_C, eval_C]
      rw [hφapply, aeval_C]
      exact (IsScalarTower.algebraMap_apply K (IntermediateField.adjoin K ({z} : Set F)) F k).symm
    · simp only [RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, Polynomial.map_X, eval_X]
      rw [hφapply, aeval_X]
      exact hzzF
  have hroot : aeval y (G.map φ) = 0 := by
    rw [aeval_def, eval₂_map, hφF, ← eval_map, ← Polynomial.map_map, map_evalRingHom_eval]
    exact hG

  have hdeg : G.natDegree ≠ 0 := by
    intro h0
    have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero h0
    have h1 : algebraMap (IntermediateField.adjoin K ({z} : Set F)) F (φ (G.coeff 0)) = 0 := by
      rw [← hroot, hGC, Polynomial.map_C, aeval_C, coeff_C_zero]
    have h2 : φ (G.coeff 0) = 0 := by
      rwa [map_eq_zero_iff _ (algebraMap (IntermediateField.adjoin K ({z} : Set F)) F).injective] at h1
    have hc : G.coeff 0 = 0 := hφinj (by rw [h2, map_zero])
    exact hGirr.ne_zero (by rw [hGC, hc, map_zero])

  have hprim : G.IsPrimitive := hGirr.isPrimitive hdeg
  have hirrQ : Irreducible (G.map (algebraMap K[X] (RatFunc K))) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := RatFunc K)).mp hGirr
  have hmapψ : Polynomial.mapEquiv (RatFunc.algEquivOfTranscendental z hz).toRingEquiv
      (G.map (algebraMap K[X] (RatFunc K))) = G.map φ := by
    rw [mapEquiv_apply, Polynomial.map_map]
    congr 1
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, ← hψ p]
    rfl
  have hirr : Irreducible (G.map φ) := by
    rw [← hmapψ]
    exact (MulEquiv.irreducible_iff _).mpr hirrQ

  have hmin := minpoly.eq_of_irreducible hirr hroot
  have hlc : (G.map φ).leadingCoeff = φ G.leadingCoeff := leadingCoeff_map_of_injective hφinj G
  have hlc0 : (G.map φ).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hirr.ne_zero
  have hGz_eq : G.map φ = C (φ G.leadingCoeff) * minpoly (IntermediateField.adjoin K ({z} : Set F)) y := by
    rw [← hmin, ← hlc, mul_comm (G.map φ), ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc0, C_1, one_mul]
  rw [hGz, hGz_eq, eval_mul, eval_C]
  rfl

end AlgebraicCurve.Place

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne.AlgebraicCurve.Place in

theorem solution
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
    (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (hrat : ∀ w : Place K F, w.IsRational)
    {z y : F} (hz : Transcendental K z)
    (G : Polynomial (Polynomial K)) (hGirr : Irreducible G)
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (Q : Place K F) (hzQ : z ∈ Q.toValuationSubring) (hyQ : y ∈ Q.toValuationSubring)
    (he : Q.ord (z - algebraMap K F (Q.evalAt z)) = 1)
    (hlead : G.leadingCoeff.eval (Q.evalAt z) ≠ 0)
    (hsep : ∀ Q' : Place K F, Q' ≠ Q → z ∈ Q'.toValuationSubring → Q'.evalAt z = Q.evalAt z →
      y ∈ Q'.toValuationSubring → Q'.evalAt y ≠ Q.evalAt y) :
    (Polynomial.derivative G).evalEval (Q.evalAt z) (Q.evalAt y) ≠ 0 := by
  haveI hfd : FiniteDimensional (IntermediateField.adjoin K ({z} : Set F)) F :=
    finiteDimensional_adjoin_of_transcendental x₀ hz
  haveI hcz : CharZero (IntermediateField.adjoin K ({z} : Set F)) :=
    charZero_of_injective_algebraMap (algebraMap K (IntermediateField.adjoin K ({z} : Set F))).injective
  haveI hsepF : Algebra.IsSeparable (IntermediateField.adjoin K ({z} : Set F)) F :=
    Algebra.IsSeparable.of_integral _ _
  set zz : IntermediateField.adjoin K ({z} : Set F) := ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
    with hzzdef
  have hzcoe : algebraMap (IntermediateField.adjoin K ({z} : Set F)) F zz = z := rfl
  have hzz : Transcendental K zz := fun h => hz (by simpa [hzcoe] using h.algebraMap (A := F))
  set ℓ : IntermediateField.adjoin K ({z} : Set F) :=
    ((G.leadingCoeff).map (algebraMap K (IntermediateField.adjoin K ({z} : Set F)))).eval zz with hℓdef
  have hℓ : algebraMap (IntermediateField.adjoin K ({z} : Set F)) F ℓ
      = ((G.leadingCoeff).map (algebraMap K F)).eval z := by
    rw [hℓdef, eval_map, hom_eval₂, ← IsScalarTower.algebraMap_eq, ← eval_map]
    rfl
  exact rf_tower hrat zz hzz y G hGirr hG ℓ hℓ (rf_gauss_minpoly hz y G hGirr hG) Q hzQ hyQ he hlead hsep

#print axioms solution

end S_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne
end P2MW
export P2MW.S_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne (solution)
