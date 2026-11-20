-- Prove2me | Definitions.Def_QECert_BK05T_AcceptedOutputIndependent
-- name    : QECert_BK05T_AcceptedOutputIndependent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:52:26.284973+00:00
-- url     : https://prove2.me/theorems/62918df3-454a-4f31-8101-a75225dbc25f
-- title:
--   Five-qubit accepted output literal slice
-- statement:
--   The two weighted conditional outputs of the five-qubit postselection construction.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L2610-L2624

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Definitions.Def_QEC_Semantics_Entropy_Convexity

set_option autoImplicit false
noncomputable section

namespace QEC.Distillation.BK05T.QECertAcceptedOutputIndependent

open QEC.Semantics QEC.Semantics.Qubit
open scoped BigOperators
open QEC.Distillation.OneQubitMagic

abbrev tZeroDirection : TDirection := tReference
def tOneDirection : TDirection :=
  ⟨fun _ => .neg, by intro i; simp⟩
noncomputable def tZero : DensityOperator QubitSpace :=
  tMagicStateOfDirection tZeroDirection
noncomputable def tOne : DensityOperator QubitSpace :=
  tMagicStateOfDirection tOneDirection
noncomputable def tInputComponent : Fin 2 → DensityOperator QubitSpace
  | 0 => tZero
  | 1 => tOne

def fiveQubitRawTZeroCoefficient (epsilon : Real) : Real :=
  (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6
def fiveQubitRawTOneCoefficient (epsilon : Real) : Real :=
  ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6
def fiveQubitSuccessProbability (epsilon : Real) : Real :=
  fiveQubitRawTZeroCoefficient epsilon +
    fiveQubitRawTOneCoefficient epsilon

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

end QEC.Distillation.BK05T.QECertAcceptedOutputIndependent


