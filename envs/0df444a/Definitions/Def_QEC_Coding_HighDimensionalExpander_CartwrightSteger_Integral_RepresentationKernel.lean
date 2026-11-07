-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T15:05:40.885826+00:00
-- url     : https://prove2.me/theorems/10df4810-cefd-4d00-8411-7b32dedb4aca
-- title:
--   Representation Kernel
-- statement:
--   Definitions and structural lemmas for Representation Kernel, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/RepresentationKernel.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantPGL_eq_of_quotientMk_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGeneratorPGL_pow_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_constant_zpow_of_skewLaurent_unit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_buildingIntegralUnitPGLHom
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_globalIntegralUnitPGLHom
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToBuildingMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToBuildingMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
theorem global_normal_data_of_eq_one
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ)
    (h : globalConstantPGLHom P r c *
        globalCyclicGeneratorPGL P r ^ n = 1) :
    (QuotientGroup.mk c : ConstantProjectiveClass P r) =
        QuotientGroup.mk 1 ∧
      n % (r.matrixRank : ℤ) = 0 := by
  have hdNat : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hd : (0 : ℤ) < (r.matrixRank : ℤ) := by exact_mod_cast hdNat
  let m : ℤ := n % (r.matrixRank : ℤ)
  have hmNonneg : 0 ≤ m := Int.emod_nonneg n (ne_of_gt hd)
  have hmLt : m < (r.matrixRank : ℤ) := Int.emod_lt_of_pos n hd
  let j : ℕ := m.toNat
  have hj : j < r.matrixRank :=
    (Int.toNat_lt_of_ne_zero (ne_of_gt hdNat)).2 hmLt
  have hmj : m = (j : ℤ) := (Int.toNat_of_nonneg hmNonneg).symm
  have hreduce : globalCyclicGeneratorPGL P r ^ n =
      globalCyclicGeneratorPGL P r ^ j := by
    calc
      _ = globalCyclicGeneratorPGL P r ^ m :=
        zpow_eq_zpow_emod' n (globalCyclicGeneratorPGL_pow_matrixRank P r)
      _ = globalCyclicGeneratorPGL P r ^ (j : ℤ) := by rw [hmj]
      _ = _ := zpow_natCast _ j
  have hcanonical :
      globalConstantPGLHom P r c * globalCyclicGeneratorPGL P r ^ j =
        globalConstantPGLHom P r 1 * globalCyclicGeneratorPGL P r ^ 0 := by
    rw [← hreduce, h]
    simp
  obtain ⟨hc, hj0⟩ := globalNormalForm_source_eq P r c 1 j 0
    hj (by exact hdNat) hcanonical
  refine ⟨hc, ?_⟩
  change m = 0
  rw [hmj, hj0]
  rfl
theorem building_normal_data_of_eq_one
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ)
    (h : buildingConstantPGLHom P r c *
        buildingCyclicGeneratorPGL P r ^ n = 1) :
    (QuotientGroup.mk c : ConstantProjectiveClass P r) =
        QuotientGroup.mk 1 ∧
      n % (r.matrixRank : ℤ) = 0 := by
  have hdNat : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hd : (0 : ℤ) < (r.matrixRank : ℤ) := by exact_mod_cast hdNat
  let m : ℤ := n % (r.matrixRank : ℤ)
  have hmNonneg : 0 ≤ m := Int.emod_nonneg n (ne_of_gt hd)
  have hmLt : m < (r.matrixRank : ℤ) := Int.emod_lt_of_pos n hd
  let j : ℕ := m.toNat
  have hj : j < r.matrixRank :=
    (Int.toNat_lt_of_ne_zero (ne_of_gt hdNat)).2 hmLt
  have hmj : m = (j : ℤ) := (Int.toNat_of_nonneg hmNonneg).symm
  have hreduce : buildingCyclicGeneratorPGL P r ^ n =
      buildingCyclicGeneratorPGL P r ^ j := by
    calc
      _ = buildingCyclicGeneratorPGL P r ^ m :=
        zpow_eq_zpow_emod' n (buildingCyclicGeneratorPGL_pow_matrixRank P r)
      _ = buildingCyclicGeneratorPGL P r ^ (j : ℤ) := by rw [hmj]
      _ = _ := zpow_natCast _ j
  have hcanonical :
      buildingConstantPGLHom P r c * buildingCyclicGeneratorPGL P r ^ j =
        buildingConstantPGLHom P r 1 * buildingCyclicGeneratorPGL P r ^ 0 := by
    rw [← hreduce, h]
    simp
  obtain ⟨hc, hj0⟩ := buildingNormalForm_source_eq P r c 1 j 0
    hj (by exact hdNat) hcanonical
  refine ⟨hc, ?_⟩
  change m = 0
  rw [hmj, hj0]
  rfl
theorem global_monomial_eq_one_iff_building_monomial_eq_one
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    globalConstantPGLHom P r c * globalCyclicGeneratorPGL P r ^ n = 1 ↔
      buildingConstantPGLHom P r c * buildingCyclicGeneratorPGL P r ^ n = 1 := by
  constructor
  · intro h
    obtain ⟨hc, hn⟩ := global_normal_data_of_eq_one P r c n h
    have hcyclic : buildingCyclicGeneratorPGL P r ^ n = 1 := by
      calc
        _ = buildingCyclicGeneratorPGL P r ^
            (n % (r.matrixRank : ℤ)) :=
          zpow_eq_zpow_emod' n
            (buildingCyclicGeneratorPGL_pow_matrixRank P r)
        _ = 1 := by rw [hn]; simp
    rw [hcyclic, mul_one]
    rw [buildingConstantPGL_eq_of_quotientMk_eq P r c 1 hc]
    exact map_one (buildingConstantPGLHom P r)
  · intro h
    obtain ⟨hc, hn⟩ := building_normal_data_of_eq_one P r c n h
    have hcyclic : globalCyclicGeneratorPGL P r ^ n = 1 := by
      calc
        _ = globalCyclicGeneratorPGL P r ^
            (n % (r.matrixRank : ℤ)) :=
          zpow_eq_zpow_emod' n
            (globalCyclicGeneratorPGL_pow_matrixRank P r)
        _ = 1 := by rw [hn]; simp
    rw [hcyclic, mul_one]
    rw [globalConstantPGL_eq_of_quotientMk_eq P r c 1 hc]
    exact map_one (globalConstantPGLHom P r)
theorem integralProjectiveRepresentation_ker_eq
    (P : BasePrime) (r : Rank) :
    (globalIntegralUnitPGLHom P r).ker =
      (buildingIntegralUnitPGLHom P r).ker := by
  ext u
  simp only [MonoidHom.mem_ker]
  obtain ⟨c, n, hu⟩ := exists_constant_zpow_of_skewLaurent_unit P r u
  have huUnit : u = skewLaurentMonomialUnit P r c n := by
    apply Units.ext
    exact hu
  rw [huUnit, globalIntegralUnitPGLHom_monomial,
    buildingIntegralUnitPGLHom_monomial]
  exact global_monomial_eq_one_iff_building_monomial_eq_one P r c n
noncomputable def globalIntegralCompactMulEquivBuildingCompact
    (P : BasePrime) (r : Rank) :
    GlobalIntegralCompactCyclicSubgroup P r ≃*
      BuildingCompactCyclicSubgroup P r := by
  rw [← range_globalIntegralUnitPGLHom P r,
    ← range_buildingIntegralUnitPGLHom P r]
  exact (QuotientGroup.quotientKerEquivRange
      (globalIntegralUnitPGLHom P r)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (integralProjectiveRepresentation_ker_eq P r)).trans
        (QuotientGroup.quotientKerEquivRange
          (buildingIntegralUnitPGLHom P r)))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


