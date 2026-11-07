-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
-- name    : QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:43:34.876898+00:00
-- url     : https://prove2.me/theorems/f60d6a64-a71a-48a5-abf1-68ab3b3175a2
-- title:
--   Local Link Reduction
-- statement:
--   Definitions and structural lemmas for Local Link Reduction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
def powerSeriesReductionGL (k : Type*) [Field k] (d : ℕ) :
    GL (Fin d) (IntegerRing k) →* GL (Fin d) k :=
  Matrix.GeneralLinearGroup.map PowerSeries.constantCoeff
def constantGeneralLinearLift (k : Type*) [Field k] (d : ℕ) :
    GL (Fin d) k →* GL (Fin d) (IntegerRing k) :=
  Matrix.GeneralLinearGroup.map PowerSeries.C
def integerGeneralLinearToPowerSeries (k : Type*) [Field k] (d : ℕ) :
    GL (Fin d) (Valued.integer (LocalFunctionField k)) →*
      GL (Fin d) (IntegerRing k) :=
  Matrix.GeneralLinearGroup.map
    (LocalTopology.powerSeriesIntegerEquiv k).symm.toRingHom
noncomputable def integerUnitOfLocalUnitOrderZero
    (k : Type*) [Field k] (c : Units (LocalFunctionField k))
    (hc : localUnitOrder c = 0) :
    Units (Valued.integer (LocalFunctionField k)) := by
  have hcint : (c : LocalFunctionField k) ∈
      Valued.integer (LocalFunctionField k) := by
    have h := integralClearingExponent_spec (c : LocalFunctionField k)
    have hclear : integralClearingExponent (c : LocalFunctionField k) = 0 := by
      change (c : LocalFunctionField k).order = 0 at hc
      rw [integralClearingExponent, hc]
      simp
    simpa [hclear] using h
  have hcinv : ((c⁻¹ : Units (LocalFunctionField k)) : LocalFunctionField k) ∈
      Valued.integer (LocalFunctionField k) := by
    have h := integralClearingExponent_spec
      ((c : LocalFunctionField k)⁻¹)
    have horder : localUnitOrder c⁻¹ = 0 := by simp [localUnitOrder_inv, hc]
    have hfieldorder : ((c : LocalFunctionField k)⁻¹).order = 0 := by
      simpa [localUnitOrder] using horder
    have hclear : integralClearingExponent
        ((c : LocalFunctionField k)⁻¹) = 0 := by
      rw [integralClearingExponent, hfieldorder]
      simp
    simpa [hclear] using h
  exact {
    val := ⟨c, hcint⟩
    inv := ⟨((c⁻¹ : Units (LocalFunctionField k)) : LocalFunctionField k), hcinv⟩
    val_inv := by ext; simp
    inv_val := by ext; simp }
def residueCoordinatePlane
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g : GL (Fin d) (IntegerRing k)) :
    FiniteGrassmannian k (Fin d → k) r := by
  let e := (Matrix.GeneralLinearGroup.toLin
    (powerSeriesReductionGL k d g)).toLinearEquiv
  exact ⟨(coordinateGrassmannian k d r hr).1.map e.toLinearMap, by
    rw [LinearEquiv.finrank_map_eq]
    exact (coordinateGrassmannian k d r hr).property⟩
def residueFundamentalPlane
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g : GL (Fin d) (IntegerRing k)) :
    FiniteGrassmannian k (Fin d → k) r := by
  let e := (Matrix.GeneralLinearGroup.toLin
    (contragredientGeneralLinearHom (powerSeriesReductionGL k d g))).toLinearEquiv
  exact ⟨(coordinateGrassmannian k d r hr).1.map e.toLinearMap, by
    rw [LinearEquiv.finrank_map_eq]
    exact (coordinateGrassmannian k d r hr).property⟩
def powerSeriesTail (k : Type*) [Field k] (f : IntegerRing k) : IntegerRing k :=
  PowerSeries.mk fun p ↦ PowerSeries.coeff (p + 1) f
def fundamentalIntegralConjugate
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    GL (Fin d) (LocalFunctionField k) :=
  (fundamentalDiagonal k d r)⁻¹ *
    powerSeriesGeneralLinearToLocal k d g *
      fundamentalDiagonal k d r
def UpperRightResidueZero
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) : Prop :=
  ∀ i j : Fin d, i.val < r → r ≤ j.val →
    PowerSeries.constantCoeff (g i j) = 0
end QEC.Coding.HighDimensionalExpander.SphericalHecke


