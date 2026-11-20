-- Prove2me | Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
-- name    : QEC_Distillation_FiveQubitT_Recurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:36:46.562772+00:00
-- url     : https://prove2.me/theorems/4ee45f6d-0b6e-4fac-bc37-444fa6cdfd40
-- title:
--   Recurrence
-- statement:
--   Definitions and structural lemmas for Recurrence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection_Part1_QECert
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tFidelity_mem_Icc

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
def bk05TRecurrence (epsilon : Real) : Real :=
  fiveQubitRawTZeroCoefficient epsilon /
    fiveQubitSuccessProbability epsilon
def bk05TOdds (epsilon : Real) : Real := epsilon / (1 - epsilon)
def bk05TThreshold : Real := (1 - Real.sqrt (3 / 7)) / 2
def bk05TThresholdPolynomial (epsilon : Real) : Real :=
  7 * epsilon ^ 2 - 7 * epsilon + 1
theorem bk05T_successProbability_pos
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    0 < fiveQubitSuccessProbability epsilon :=
  by
    have hcomplement : 0 < 1 - epsilon := by linarith
    have hcomplementNonneg : 0 ≤ 1 - epsilon := hcomplement.le
    have hpower : 0 < (1 - epsilon) ^ 5 := pow_pos hcomplement _
    have hden : 0 < (6 : Real) := by norm_num
    have hfirst : 0 ≤ epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3 := by
      positivity
    have hsecond : 0 ≤ 5 * epsilon ^ 3 * (1 - epsilon) ^ 2 := by positivity
    unfold fiveQubitSuccessProbability fiveQubitRawTZeroCoefficient fiveQubitRawTOneCoefficient
    exact add_pos_of_nonneg_of_pos (div_nonneg hfirst hden.le)
      (div_pos (add_pos_of_pos_of_nonneg hpower hsecond) hden)
theorem bk05TRecurrence_nonneg
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    0 <= bk05TRecurrence epsilon := by
  have hcomplement : 0 ≤ 1 - epsilon := by linarith
  have hraw : 0 ≤ fiveQubitRawTZeroCoefficient epsilon := by
    unfold fiveQubitRawTZeroCoefficient
    positivity
  exact div_nonneg hraw (bk05T_successProbability_pos epsilon hzero hhalf).le
theorem rawCoefficient_difference_factor
    (epsilon : Real) :
    fiveQubitRawTOneCoefficient epsilon -
        fiveQubitRawTZeroCoefficient epsilon =
      ((1 - 2 * epsilon) ^ 3 *
        (1 + epsilon * (1 - epsilon))) / 6 := by
  unfold fiveQubitRawTOneCoefficient fiveQubitRawTZeroCoefficient
  ring
theorem bk05TRecurrence_le_half
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk05TRecurrence epsilon <= 1 / 2 := by
  have hcomplement : 0 <= 1 - epsilon := by linarith
  have hlinear : 0 <= 1 - 2 * epsilon := by linarith
  have hfactor :
      0 <= (1 - 2 * epsilon) ^ 3 *
        (1 + epsilon * (1 - epsilon)) := by positivity
  have hcoeff :
      fiveQubitRawTZeroCoefficient epsilon <=
        fiveQubitRawTOneCoefficient epsilon := by
    have hdiff := rawCoefficient_difference_factor epsilon
    have hfactor' :
        0 <= ((1 - 2 * epsilon) ^ 3 *
          (1 + epsilon * (1 - epsilon))) / 6 := by positivity
    linarith
  have hsuccess := bk05T_successProbability_pos epsilon hzero hhalf
  rw [bk05TRecurrence, div_le_iff₀ hsuccess]
  unfold fiveQubitSuccessProbability
  linarith
def bk05TIteration (epsilon : Real) (rounds : Nat) : Real :=
  (bk05TRecurrence^[rounds]) epsilon
def bk05TFidelityError (rho : DensityOperator QubitSpace) : Real :=
  1 - tFidelity rho ^ 2
def bk05TFidelityThreshold : Real :=
  Real.sqrt ((1 + Real.sqrt (3 / 7)) / 2)
theorem bk05TFidelityError_nonneg (rho : DensityOperator QubitSpace) :
    0 <= bk05TFidelityError rho := by
  have hfidelity := tFidelity_mem_Icc rho
  unfold bk05TFidelityError
  nlinarith [hfidelity.1, hfidelity.2, sq_nonneg (tFidelity rho)]
theorem bk05TFidelityError_le_one (rho : DensityOperator QubitSpace) :
    bk05TFidelityError rho <= 1 := by
  unfold bk05TFidelityError
  nlinarith [sq_nonneg (tFidelity rho)]
def qubitDensityBloch (rho : DensityOperator QubitSpace) :
    PauliAxis -> Real
  | .x => 2 * (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      rho.toOperator 0 1).re
  | .y => -2 * (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      rho.toOperator 0 1).im
  | .z => 2 * (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      (EuclideanSpace.basisFun (Fin 2) Complex).toBasis
      rho.toOperator 0 0).re - 1
end BK05T
end Distillation
end QEC


