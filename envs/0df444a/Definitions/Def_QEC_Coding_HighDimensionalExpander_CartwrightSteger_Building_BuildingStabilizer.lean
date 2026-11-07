-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:56:51.448048+00:00
-- url     : https://prove2.me/theorems/f78fd582-254d-40ab-b06f-3ae1a6ac26a6
-- title:
--   Building Stabilizer
-- statement:
--   Definitions and structural lemmas for Building Stabilizer, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGeneratorMatrix_mul_buildingConstantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
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
noncomputable def constantFrobeniusUnitEquiv
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ ≃* (ConstantExtension P r)ˣ :=
  Units.mapEquiv (constantFrobenius P r).toMulEquiv
@[simp]
theorem constantFrobeniusUnitEquiv_coe
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (constantFrobeniusUnitEquiv P r u : ConstantExtension P r) =
      constantFrobenius P r u :=
  rfl
noncomputable def buildingConstantGLHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  (Matrix.GeneralLinearGroup.map
      (algebraMap (BaseField P) (BuildingLocalField P))).comp
    (Units.map (constantRegularMatrix P r).toMonoidHom)
@[simp]
theorem buildingConstantGLHom_apply
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingConstantGLHom P r u = buildingConstantGL P r u :=
  rfl
noncomputable def buildingConstantPGLHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.ProjGenLinGroup.mk.comp (buildingConstantGLHom P r)
noncomputable def buildingCyclicGeneratorPGL
    (P : BasePrime) (r : Rank) :
    Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.ProjGenLinGroup.mk (buildingCyclicGeneratorGL P r)
theorem buildingCyclicGeneratorGL_conj_constant
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorGL P r * buildingConstantGL P r u *
        (buildingCyclicGeneratorGL P r)⁻¹ =
      buildingConstantGL P r (constantFrobeniusUnitEquiv P r u) := by
  apply mul_right_cancel (b := buildingCyclicGeneratorGL P r)
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  apply Units.ext
  simp only [Units.val_mul]
  rw [buildingCyclicGeneratorGL_coe, buildingConstantGL_coe,
    buildingConstantGL_coe, constantFrobeniusUnitEquiv_coe]
  exact buildingCyclicGeneratorMatrix_mul_buildingConstantMatrix P r u
theorem buildingCyclicGeneratorPGL_conj_constant
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorPGL P r * buildingConstantPGLHom P r u *
        (buildingCyclicGeneratorPGL P r)⁻¹ =
      buildingConstantPGLHom P r (constantFrobeniusUnitEquiv P r u) := by
  exact congrArg (Matrix.ProjGenLinGroup.mk :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) →*
        Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (buildingCyclicGeneratorGL_conj_constant P r u)
theorem buildingCyclicGeneratorPGL_zpow_conj_constant
    (P : BasePrime) (r : Rank) (n : ℤ)
    (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorPGL P r ^ n *
        buildingConstantPGLHom P r u *
        (buildingCyclicGeneratorPGL P r ^ n)⁻¹ =
      buildingConstantPGLHom P r
        ((constantFrobeniusUnitEquiv P r ^ n) u) := by
  induction n using Int.induction_on generalizing u with
  | zero => simp
  | succ n ih =>
      calc
        buildingCyclicGeneratorPGL P r ^ ((n : ℤ) + 1) *
              buildingConstantPGLHom P r u *
              (buildingCyclicGeneratorPGL P r ^ ((n : ℤ) + 1))⁻¹ =
            buildingCyclicGeneratorPGL P r ^ (n : ℤ) *
              (buildingCyclicGeneratorPGL P r *
                buildingConstantPGLHom P r u *
                (buildingCyclicGeneratorPGL P r)⁻¹) *
              (buildingCyclicGeneratorPGL P r ^ (n : ℤ))⁻¹ := by
                rw [zpow_add_one]
                group
        _ = buildingCyclicGeneratorPGL P r ^ (n : ℤ) *
              buildingConstantPGLHom P r
                (constantFrobeniusUnitEquiv P r u) *
              (buildingCyclicGeneratorPGL P r ^ (n : ℤ))⁻¹ := by
                rw [buildingCyclicGeneratorPGL_conj_constant]
        _ = buildingConstantPGLHom P r
              ((constantFrobeniusUnitEquiv P r ^ (n : ℤ))
                (constantFrobeniusUnitEquiv P r u)) :=
              ih (constantFrobeniusUnitEquiv P r u)
        _ = buildingConstantPGLHom P r
              ((constantFrobeniusUnitEquiv P r ^ ((n : ℤ) + 1)) u) := by
                rw [zpow_add_one, MulAut.mul_apply]
  | pred n ih =>
      have hinverse (v : (ConstantExtension P r)ˣ) :
          (buildingCyclicGeneratorPGL P r)⁻¹ *
              buildingConstantPGLHom P r v *
              buildingCyclicGeneratorPGL P r =
            buildingConstantPGLHom P r
              ((constantFrobeniusUnitEquiv P r)⁻¹ v) := by
        have hforward := buildingCyclicGeneratorPGL_conj_constant P r
          ((constantFrobeniusUnitEquiv P r)⁻¹ v)
        have hforward' :
            buildingCyclicGeneratorPGL P r *
                buildingConstantPGLHom P r
                  ((constantFrobeniusUnitEquiv P r)⁻¹ v) *
                (buildingCyclicGeneratorPGL P r)⁻¹ =
              buildingConstantPGLHom P r v := by
          simpa using hforward
        calc
          (buildingCyclicGeneratorPGL P r)⁻¹ *
                buildingConstantPGLHom P r v *
                buildingCyclicGeneratorPGL P r =
              (buildingCyclicGeneratorPGL P r)⁻¹ *
                (buildingCyclicGeneratorPGL P r *
                  buildingConstantPGLHom P r
                    ((constantFrobeniusUnitEquiv P r)⁻¹ v) *
                  (buildingCyclicGeneratorPGL P r)⁻¹) *
                buildingCyclicGeneratorPGL P r := by rw [hforward']
          _ = buildingConstantPGLHom P r
                ((constantFrobeniusUnitEquiv P r)⁻¹ v) := by group
      change buildingCyclicGeneratorPGL P r ^ (-(n : ℤ) - 1) *
            buildingConstantPGLHom P r u *
            (buildingCyclicGeneratorPGL P r ^ (-(n : ℤ) - 1))⁻¹ =
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ) - 1)) u)
      calc
        buildingCyclicGeneratorPGL P r ^ (-(n : ℤ) - 1) *
              buildingConstantPGLHom P r u *
              (buildingCyclicGeneratorPGL P r ^ (-(n : ℤ) - 1))⁻¹ =
            buildingCyclicGeneratorPGL P r ^ (-(n : ℤ)) *
              ((buildingCyclicGeneratorPGL P r)⁻¹ *
                buildingConstantPGLHom P r u *
                buildingCyclicGeneratorPGL P r) *
              (buildingCyclicGeneratorPGL P r ^ (-(n : ℤ)))⁻¹ := by
                rw [zpow_sub_one]
                group
        _ = buildingCyclicGeneratorPGL P r ^ (-(n : ℤ)) *
              buildingConstantPGLHom P r
                ((constantFrobeniusUnitEquiv P r)⁻¹ u) *
              (buildingCyclicGeneratorPGL P r ^ (-(n : ℤ)))⁻¹ := by
                rw [hinverse]
        _ = buildingConstantPGLHom P r
              ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ)))
                ((constantFrobeniusUnitEquiv P r)⁻¹ u)) :=
              ih ((constantFrobeniusUnitEquiv P r)⁻¹ u)
        _ = buildingConstantPGLHom P r
              ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ) - 1)) u) := by
                rw [zpow_sub_one, MulAut.mul_apply]
noncomputable def constantFrobeniusZAction
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →* MulAut ((ConstantExtension P r)ˣ) :=
  zpowersHom _ (constantFrobeniusUnitEquiv P r)
noncomputable def buildingCyclicZHom
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  zpowersHom _ (buildingCyclicGeneratorPGL P r)
theorem buildingConstant_cyclic_compatibility
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ) :
    (buildingConstantPGLHom P r).comp
        ((constantFrobeniusZAction P r n).toMonoidHom) =
      (MulAut.conj (buildingCyclicZHom P r n)).toMonoidHom.comp
        (buildingConstantPGLHom P r) := by
  ext u
  change buildingConstantPGLHom P r
      ((constantFrobeniusUnitEquiv P r ^ n.toAdd) u) =
    buildingCyclicGeneratorPGL P r ^ n.toAdd *
      buildingConstantPGLHom P r u *
      (buildingCyclicGeneratorPGL P r ^ n.toAdd)⁻¹
  exact (buildingCyclicGeneratorPGL_zpow_conj_constant
    P r n.toAdd u).symm
abbrev BuildingCompactCyclicSemidirect
    (P : BasePrime) (r : Rank) :=
  (ConstantExtension P r)ˣ ⋊[constantFrobeniusZAction P r] Multiplicative ℤ
noncomputable def buildingCompactCyclicSemidirectHom
    (P : BasePrime) (r : Rank) :
    BuildingCompactCyclicSemidirect P r →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  SemidirectProduct.lift
    (buildingConstantPGLHom P r)
    (buildingCyclicZHom P r)
    (buildingConstant_cyclic_compatibility P r)
noncomputable def compactConjugationDiagonalUnit
    (P : BasePrime) (r : Rank) (u v : (ConstantExtension P r)ˣ)
    (j k : ℕ) :
    (ConstantExtension P r)ˣ :=
  u * ((constantFrobeniusUnitEquiv P r ^ j) v) *
    ((constantFrobeniusUnitEquiv P r ^ k) u)⁻¹
noncomputable def compactConjugationDiagonalMultiplier
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (k : ℕ) :
    ConstantExtension P r :=
  (u : ConstantExtension P r) *
    ((constantFrobenius P r ^ k) (u : ConstantExtension P r))⁻¹
noncomputable def compactConjugationDiagonalBlock
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (j k : ℕ) :
    ConstantExtension P r →ₗ[BaseField P] ConstantExtension P r :=
  (Algebra.lmul (BaseField P) (ConstantExtension P r)
      (compactConjugationDiagonalMultiplier P r u k)).comp
    (constantFrobenius P r ^ j).toLinearEquiv.toLinearMap
def CompactNormalFormHasIdentityDiagonal
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ) :
    Prop :=
  ∀ k : Fin r.matrixRank,
    compactConjugationDiagonalBlock P r u j k = LinearMap.id
def BuildingElementHasIdentityConjugationDiagonal
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) :
    Prop :=
  ∀ (u : (ConstantExtension P r)ˣ) (j : ℕ),
    j < r.matrixRank →
    g = buildingConstantPGLHom P r u *
      buildingCyclicGeneratorPGL P r ^ j →
    CompactNormalFormHasIdentityDiagonal P r u j
noncomputable def BuildingCompactCyclicSubgroup
    (P : BasePrime) (r : Rank) :
    Subgroup
      (Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) :=
  Subgroup.closure
    (Set.range (buildingConstantPGLHom P r) ∪
      {buildingCyclicGeneratorPGL P r})
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


