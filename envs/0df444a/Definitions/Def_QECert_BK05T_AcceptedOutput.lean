-- Prove2me | Definitions.Def_QECert_BK05T_AcceptedOutput
-- name    : QECert_BK05T_AcceptedOutput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:40:50.968877+00:00
-- url     : https://prove2.me/theorems/a3b297c8-d51c-4098-8b38-3bf02fd52bce
-- title:
--   Five-qubit accepted output
-- statement:
--   The two weighted conditional outputs of the five-qubit postselection construction.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L2610-L2624

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection_Part1_QECert

set_option autoImplicit false
noncomputable section

namespace QEC.Distillation.BK05T.QECertAcceptedOutput

open QEC.Semantics QEC.Semantics.Qubit
open scoped BigOperators

def fiveQubitAcceptedOutputWeight (epsilon : Real) : Fin 2 → Real
  | 0 => fiveQubitRawTOneCoefficient epsilon /
      fiveQubitSuccessProbability epsilon
  | 1 => fiveQubitRawTZeroCoefficient epsilon /
      fiveQubitSuccessProbability epsilon

private theorem coefficientZero_nonneg (epsilon : Real)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 ≤ fiveQubitRawTZeroCoefficient epsilon := by
  have hcomp : 0 ≤ 1 - epsilon := sub_nonneg.mpr hone
  unfold fiveQubitRawTZeroCoefficient
  positivity

private theorem coefficientOne_nonneg (epsilon : Real)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 ≤ fiveQubitRawTOneCoefficient epsilon := by
  have hcomp : 0 ≤ 1 - epsilon := sub_nonneg.mpr hone
  unfold fiveQubitRawTOneCoefficient
  positivity

private theorem success_pos (epsilon : Real) (hzero : 0 ≤ epsilon)
    (hone : epsilon ≤ 1) : 0 < fiveQubitSuccessProbability epsilon := by
  have hcomp : 0 ≤ 1 - epsilon := sub_nonneg.mpr hone
  unfold fiveQubitSuccessProbability fiveQubitRawTZeroCoefficient
    fiveQubitRawTOneCoefficient
  by_cases hhalf : epsilon ≤ 1 / 2
  · have hpow : 0 < (1 - epsilon) ^ 5 := pow_pos (by linarith) _
    positivity
  · have hpow : 0 < epsilon ^ 5 := pow_pos (by linarith) _
    positivity

private theorem weight_nonneg (epsilon : Real) (hzero : 0 ≤ epsilon)
    (hone : epsilon ≤ 1) (word : Fin 2) :
    0 ≤ fiveQubitAcceptedOutputWeight epsilon word := by
  have hden := (success_pos epsilon hzero hone).le
  fin_cases word
  · exact div_nonneg (coefficientOne_nonneg epsilon hzero hone) hden
  · exact div_nonneg (coefficientZero_nonneg epsilon hzero hone) hden

private theorem weight_sum (epsilon : Real) (hzero : 0 ≤ epsilon)
    (hone : epsilon ≤ 1) :
    ∑ word : Fin 2, fiveQubitAcceptedOutputWeight epsilon word = 1 := by
  have hd := (success_pos epsilon hzero hone).ne'
  rw [Fin.sum_univ_two]
  change fiveQubitRawTOneCoefficient epsilon / fiveQubitSuccessProbability epsilon +
    fiveQubitRawTZeroCoefficient epsilon / fiveQubitSuccessProbability epsilon = 1
  rw [← add_div, add_comm]
  exact div_self hd

def fiveQubitAcceptedOutput (epsilon : Real) (hzero : 0 ≤ epsilon)
    (hone : epsilon ≤ 1) : DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ
    (fiveQubitAcceptedOutputWeight epsilon) tInputComponent
    (fun word _ => weight_nonneg epsilon hzero hone word)
    (by simpa using weight_sum epsilon hzero hone)

end QEC.Distillation.BK05T.QECertAcceptedOutput


