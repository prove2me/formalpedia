-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T13:30:57.414673+00:00
-- url     : https://prove2.me/theorems/828a7d97-c8d6-4e0a-8816-eb488be5fbf0
-- title:
--   Building Skew Representation
-- statement:
--   Definitions and structural lemmas for Building Skew Representation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingSkewRepresentation.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCompactNormalForm
import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
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
theorem constantFrobeniusUnitEquiv_zpow_coe
    (P : BasePrime) (r : Rank) (n : ℤ)
    (u : (ConstantExtension P r)ˣ) :
    (((constantFrobeniusUnitEquiv P r ^ n) u :
        (ConstantExtension P r)ˣ) : ConstantExtension P r) =
      Multiplicative.ofAdd n • (u : ConstantExtension P r) := by
  change _ = constantFrobeniusZRingAction P r (Multiplicative.ofAdd n) u
  rw [constantFrobeniusZRingAction, zpowersHom_apply]
  induction n using Int.induction_on generalizing u with
  | zero => simp
  | succ n ih =>
      change _ = ((constantFrobenius P r).toRingEquiv ^ ((n : ℤ) + 1)) u
      rw [zpow_add_one, MulAut.mul_apply, zpow_add_one, RingAut.mul_apply]
      rw [ih, constantFrobeniusUnitEquiv_coe]
      simp
  | pred n ih =>
      change _ = ((constantFrobenius P r).toRingEquiv ^ (-(n : ℤ) - 1)) u
      rw [zpow_sub_one, MulAut.mul_apply, zpow_sub_one, RingAut.mul_apply]
      rw [ih]
      rfl
theorem buildingCyclicGeneratorGL_zpow_conj_constant
    (P : BasePrime) (r : Rank) (n : ℤ)
    (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorGL P r ^ n * buildingConstantGL P r u *
        (buildingCyclicGeneratorGL P r ^ n)⁻¹ =
      buildingConstantGL P r
        ((constantFrobeniusUnitEquiv P r ^ n) u) := by
  induction n using Int.induction_on generalizing u with
  | zero => simp
  | succ n ih =>
      calc
        buildingCyclicGeneratorGL P r ^ ((n : ℤ) + 1) *
              buildingConstantGL P r u *
              (buildingCyclicGeneratorGL P r ^ ((n : ℤ) + 1))⁻¹ =
            buildingCyclicGeneratorGL P r ^ (n : ℤ) *
              (buildingCyclicGeneratorGL P r *
                buildingConstantGL P r u *
                (buildingCyclicGeneratorGL P r)⁻¹) *
              (buildingCyclicGeneratorGL P r ^ (n : ℤ))⁻¹ := by
                rw [zpow_add_one]
                group
        _ = buildingCyclicGeneratorGL P r ^ (n : ℤ) *
              buildingConstantGL P r
                (constantFrobeniusUnitEquiv P r u) *
              (buildingCyclicGeneratorGL P r ^ (n : ℤ))⁻¹ := by
                rw [buildingCyclicGeneratorGL_conj_constant]
        _ = buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r ^ (n : ℤ))
                (constantFrobeniusUnitEquiv P r u)) :=
              ih (constantFrobeniusUnitEquiv P r u)
        _ = buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r ^ ((n : ℤ) + 1)) u) := by
                rw [zpow_add_one, MulAut.mul_apply]
  | pred n ih =>
      have hinverse (v : (ConstantExtension P r)ˣ) :
          (buildingCyclicGeneratorGL P r)⁻¹ *
              buildingConstantGL P r v *
              buildingCyclicGeneratorGL P r =
            buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r)⁻¹ v) := by
        have hforward := buildingCyclicGeneratorGL_conj_constant P r
          ((constantFrobeniusUnitEquiv P r)⁻¹ v)
        have hforward' :
            buildingCyclicGeneratorGL P r *
                buildingConstantGL P r
                  ((constantFrobeniusUnitEquiv P r)⁻¹ v) *
                (buildingCyclicGeneratorGL P r)⁻¹ =
              buildingConstantGL P r v := by
          simpa using hforward
        calc
          (buildingCyclicGeneratorGL P r)⁻¹ *
                buildingConstantGL P r v *
                buildingCyclicGeneratorGL P r =
              (buildingCyclicGeneratorGL P r)⁻¹ *
                (buildingCyclicGeneratorGL P r *
                  buildingConstantGL P r
                    ((constantFrobeniusUnitEquiv P r)⁻¹ v) *
                  (buildingCyclicGeneratorGL P r)⁻¹) *
                buildingCyclicGeneratorGL P r := by rw [hforward']
          _ = buildingConstantGL P r
                ((constantFrobeniusUnitEquiv P r)⁻¹ v) := by group
      change buildingCyclicGeneratorGL P r ^ (-(n : ℤ) - 1) *
            buildingConstantGL P r u *
            (buildingCyclicGeneratorGL P r ^ (-(n : ℤ) - 1))⁻¹ =
        buildingConstantGL P r
          ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ) - 1)) u)
      calc
        buildingCyclicGeneratorGL P r ^ (-(n : ℤ) - 1) *
              buildingConstantGL P r u *
              (buildingCyclicGeneratorGL P r ^ (-(n : ℤ) - 1))⁻¹ =
            buildingCyclicGeneratorGL P r ^ (-(n : ℤ)) *
              ((buildingCyclicGeneratorGL P r)⁻¹ *
                buildingConstantGL P r u *
                buildingCyclicGeneratorGL P r) *
              (buildingCyclicGeneratorGL P r ^ (-(n : ℤ)))⁻¹ := by
                rw [zpow_sub_one]
                group
        _ = buildingCyclicGeneratorGL P r ^ (-(n : ℤ)) *
              buildingConstantGL P r
                ((constantFrobeniusUnitEquiv P r)⁻¹ u) *
              (buildingCyclicGeneratorGL P r ^ (-(n : ℤ)))⁻¹ := by
                rw [hinverse]
        _ = buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ)))
                ((constantFrobeniusUnitEquiv P r)⁻¹ u)) :=
              ih ((constantFrobeniusUnitEquiv P r)⁻¹ u)
        _ = buildingConstantGL P r
              ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ) - 1)) u) := by
                rw [zpow_sub_one, MulAut.mul_apply]
noncomputable def buildingConstantMatrixEmbedding
    (P : BasePrime) (r : Rank) :
    ConstantExtension P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) where
  toFun := buildingConstantMatrix P r
  map_zero' := by simp [buildingConstantMatrix]
  map_one' := by simp [buildingConstantMatrix]
  map_add' c d := by
    ext i j
    simp [buildingConstantMatrix]
  map_mul' c d := by
    rw [buildingConstantMatrix, buildingConstantMatrix, buildingConstantMatrix,
      ← Matrix.map_mul, map_mul]
@[simp] theorem buildingConstantMatrixEmbedding_apply
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    buildingConstantMatrixEmbedding P r c =
      buildingConstantMatrix P r c := rfl
noncomputable def buildingCyclicZGLHom
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  zpowersHom _ (buildingCyclicGeneratorGL P r)
noncomputable def buildingCyclicZMatrixHom
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  (Units.coeHom _).comp (buildingCyclicZGLHom P r)
@[simp] theorem buildingCyclicZMatrixHom_apply
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ) :
    buildingCyclicZMatrixHom P r n =
      ((buildingCyclicGeneratorGL P r) ^ n.toAdd :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :=
  rfl
theorem buildingCyclic_zpow_conj_constant
    (P : BasePrime) (r : Rank) (n : ℤ)
    (c : ConstantExtension P r) :
    ((buildingCyclicGeneratorGL P r ^ n :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) *
        buildingConstantMatrix P r c *
        (((buildingCyclicGeneratorGL P r ^ n)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) =
      buildingConstantMatrix P r (Multiplicative.ofAdd n • c) := by
  by_cases hc : c = 0
  · simp [hc, buildingConstantMatrix]
  · let u : (ConstantExtension P r)ˣ := Units.mk0 c hc
    have h := buildingCyclicGeneratorGL_zpow_conj_constant P r n u
    have hval := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul, buildingConstantGL_coe,
      buildingConstantGL_coe] at hval
    have hcoe : (((constantFrobeniusUnitEquiv P r ^ n) u :
          (ConstantExtension P r)ˣ) : ConstantExtension P r) =
        Multiplicative.ofAdd n • (u : ConstantExtension P r) :=
      constantFrobeniusUnitEquiv_zpow_coe P r n u
    calc
      _ = buildingConstantMatrix P r
          (((constantFrobeniusUnitEquiv P r ^ n) u :
            (ConstantExtension P r)ˣ) : ConstantExtension P r) := by
              simpa [u] using hval
      _ = _ := congrArg (buildingConstantMatrix P r) hcoe
theorem buildingSkewLaurent_compatibility
    (P : BasePrime) (r : Rank)
    {c : ConstantExtension P r} {n : Multiplicative ℤ} :
    buildingConstantMatrixEmbedding P r (n • c) *
        buildingCyclicZMatrixHom P r n =
      buildingCyclicZMatrixHom P r n *
        buildingConstantMatrixEmbedding P r c := by
  have hconj := buildingCyclic_zpow_conj_constant P r n.toAdd c
  rw [buildingCyclicZMatrixHom_apply,
    buildingConstantMatrixEmbedding_apply,
    buildingConstantMatrixEmbedding_apply]
  have haction : n • c = Multiplicative.ofAdd n.toAdd • c := by
    congr 1
  rw [haction]
  calc
    buildingConstantMatrix P r (Multiplicative.ofAdd n.toAdd • c) *
        ((buildingCyclicGeneratorGL P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix _ _ _) =
      (((buildingCyclicGeneratorGL P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix _ _ _) * buildingConstantMatrix P r c *
        (((buildingCyclicGeneratorGL P r ^ n.toAdd)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix _ _ _)) *
        ((buildingCyclicGeneratorGL P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix _ _ _) := by rw [hconj]
    _ = ((buildingCyclicGeneratorGL P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix _ _ _) * buildingConstantMatrix P r c := by
      simp only [mul_assoc]
      rw [← Units.val_mul]
      simp
noncomputable def skewLaurentToBuildingMatrix
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSkewLaurentRing P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  SkewMonoidAlgebra.liftNCRingHom
    (buildingConstantMatrixEmbedding P r)
    (buildingCyclicZMatrixHom P r)
    (fun {_ _} => buildingSkewLaurent_compatibility P r)
noncomputable def buildingIntegralUnitGLHom
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerSkewLaurentRing P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Units.map (skewLaurentToBuildingMatrix P r).toMonoidHom
noncomputable def buildingIntegralUnitPGLHom
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerSkewLaurentRing P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.ProjGenLinGroup.mk.comp (buildingIntegralUnitGLHom P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


