-- Prove2me | Definitions.Def_OAI_PiExponent_LiteralAnalytic_choiceScalarMajorant
-- name    : OAI_PiExponent_LiteralAnalytic_choiceScalarMajorant
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T12:00:12.022907+00:00
-- url     : https://prove2.me/theorems/e5dab64d-02fe-4798-a21b-ed7dbbb2dde6
-- title:
--   Explicit product majorant for a translated row scalar
-- statement:
--   Package the natural binomial product, norms of the translated-coordinate powers, and the norm of the logarithmic-tail coefficient as a real-valued majorant.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

namespace OAI.PiExponent.LiteralAnalytic

noncomputable def choiceScalarMajorant {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) : ℝ :=
  ((∏ i : Fin d.m,
      (t.1.1 i).choose (beta d r i) *
        (t.1.1 i - beta d r i).choose (t.2.1 i) : ℕ) : ℝ) *
    (∏ i : Fin d.m,
      ‖(r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          logarithmicPeriod)‖ ^
        (t.1.1 i - beta d r i - t.2.1 i)) *
    ‖PowerSeries.coeff t.2.2
      (∏ i : Fin d.m,
        (RowTranslation.tail
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
          (PowerSeries.log ℂ)) ^ (t.2.1 i : ℕ))‖

end OAI.PiExponent.LiteralAnalytic


