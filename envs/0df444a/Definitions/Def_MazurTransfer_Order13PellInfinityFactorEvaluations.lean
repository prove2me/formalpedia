-- Prove2me | Definitions.Def_MazurTransfer_Order13PellInfinityFactorEvaluations
-- name    : MazurTransfer_Order13PellInfinityFactorEvaluations
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:29:01.578859+00:00
-- url     : https://prove2.me/theorems/527635b4-18f8-4930-8431-b6020aa3ebc8
-- title:
--   The actual Pell factors evaluated at either infinity point
-- statement:
--   Let $R$ be a commutative ring and let $a\in R$ satisfy $a^2=1$. At the literal infinity point $(z,w)=(0,a)$, the two specified reciprocal Pell factors satisfy $$P_{\infty,+}(0,a)=1+a,\qquad P_{\infty,-}(0,a)=1-a.$$ These exact evaluations identify the unit factor at each infinity point and supply the local valuation computation.
-- source:
--   Original complete two reciprocal Pell factor evaluation statements and proofs from MazurTheorem Order13PellChartCertificate.lean, Apache-2.0, Vas and contributors. The two complete original types are kernel-compared; there are no data-valued definitions. The original coordinate evaluation helpers are inlined with explicit public abbreviation unfolding; only their namespace qualifications change in the two main proof bodies. Named downstream consumer: actual Pell infinity valuations.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Polynomial coefficients and Pell identities adapted from MazurTheorem,
MazurTorsion/NumberTheory/XOneThirteenDescent.lean, user source pin
54d43d8dda8a6fcf069cc02a815f850d762c5c0c; source SHA-256
10a30be619946d1c2a3207bffb758840f80ff71dcbb0ee5c3dd0d068cc80961f.
Design boundary: the literal Pell polynomial certificate over arbitrary
commutative rings and its evaluation on the two actual coordinate charts.
Named downstream consumer: the actual degree-19 principal-divisor computation.
-/
import Definitions.Def_MazurTransfer_Order13PellCoordinateFactors
import Definitions.Def_MazurTransfer_Order13InfinityEvaluationMaps
noncomputable section
universe u
namespace MazurTransfer.PellInfinityEvaluationHelpers20261017
open Polynomial MazurTransfer.Order13IntegralSections
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]
theorem reciprocalInfinityEvaluation_z (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (zCoordinate R) = 0 := by
  simp [reciprocalInfinityEvaluation, InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation, zCoordinate, AdjoinRoot.lift_of]

theorem reciprocalInfinityEvaluation_w (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (wCoordinate R) = a := by
  simp [reciprocalInfinityEvaluation, InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation, wCoordinate, AdjoinRoot.lift_root]
end MazurTransfer.PellInfinityEvaluationHelpers20261017
namespace MazurTransfer.Order13PellChartCertificate
theorem reciprocalPlus_evaluation (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1) :
    Order13InfinityEvaluationKernel.evaluation R a ha (reciprocalPlus R) = 1 + a := by
  simp [reciprocalPlus, infinityPellH, infinityPellK,
    Order13InfinityEvaluationKernel.evaluation,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_z,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_w]

theorem reciprocalMinus_evaluation (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1) :
    Order13InfinityEvaluationKernel.evaluation R a ha (reciprocalMinus R) = 1 - a := by
  simp [reciprocalMinus, infinityPellH, infinityPellK,
    Order13InfinityEvaluationKernel.evaluation,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_z,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_w]

end MazurTransfer.Order13PellChartCertificate
#print axioms MazurTransfer.Order13PellChartCertificate.reciprocalPlus_evaluation
#print axioms MazurTransfer.Order13PellChartCertificate.reciprocalMinus_evaluation


