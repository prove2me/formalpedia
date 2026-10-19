-- Prove2me | Definitions.Def_OAI_PiExponent_FiniteActualTranslation
-- name    : OAI_PiExponent_FiniteActualTranslation
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-18T12:23:52.836987+00:00
-- url     : https://prove2.me/theorems/2ff4acde-8169-44e7-8f55-2228124d3061
-- title:
--   Finite translation data compatible with the actual determinant family
-- statement:
--   Defines finite function-indexed translation choices, their scalar factors, formal period coefficient matrices, determinant summands, index weights, and collision allowance using the unchanged parent definition bundle. Truncation retains exactly the degrees strictly below its order.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean, formal_period_collision_bound; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean, translated_summand_bound and log_norm_sum_le; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean, translationTermCount. Synthesized explicit actual-matrix bridge obligation for Approximation/DeterminantContradiction.lean, AnalyticAggregateStatement; not claimed to be proved by those source lemmas.

import Definitions.Def_OAI_PiExponent_AnalyticRemainder
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators

noncomputable section

namespace OAI.PiExponent.DeterminantContradiction.FiniteTranslation

-- Function-indexed translation data for the FixedDeterminantFamily bundle.
-- The older LiteralAnalytic interface redeclares the parent constants in a
-- different definition bundle and cannot be imported alongside this one.
abbrev Index {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ↥(realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d)) H)

abbrev Choice {nu : ℝ} (d : FixedData nu) (H : ℝ) (r : Row d H) :=
  Σ a : Index d H,
    (∀ i : Fin d.m, Fin (a.1 i - r.2.1 i.succ + 1)) × Fin (r.2.1 0 + 1)

abbrev Family {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ∀ r : Row d H, Choice d H r

def weight {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Index d H) : ℝ :=
  ∑ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i * (a.1 i : ℝ)

def periodModel {m : ℕ} (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) :=
  MvPolynomial.C ((1 + PowerSeries.X) ^ h) *
    ∏ i, (MvPolynomial.C
      (PowerSeries.C ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) + PowerSeries.log ℂ) +
      MvPolynomial.X i) ^ a i

def scalar {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : Choice d H r) : ℂ :=
  ((∏ i : Fin d.m, (t.1.1 i).choose (r.2.1 i.succ) *
      (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ) *
    (∏ i : Fin d.m,
      ((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          2 * (Real.pi : ℂ) * Complex.I)) ^
            (t.1.1 i - r.2.1 i.succ - t.2.1 i)) *
    PowerSeries.coeff (t.2.2 : ℕ)
      (∏ i : Fin d.m,
        ((PowerSeries.trunc
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
          (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^ (t.2.1 i : ℕ))

def coefficientMatrix {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : Family d H) :
    Matrix (Row d H) (Row d H) ℂ :=
  fun r c => PowerSeries.coeff (r.2.1 0 - (f r).2.2)
    ((periodModel r.1.val ((selection c).1 0)
      (fun i => (selection c).1 i.succ)).coeff
        (InterpolationMatrix.exponentVector (f r).1.1))

def term {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : Family d H) : ℂ :=
  (∏ r : Row d H, scalar d r (f r)) * (coefficientMatrix d selection f).det

def collisionAllowance (M : ℕ) (H : ℝ) : ℝ :=
  (Real.log (M : ℝ) + Real.log 2 / 4 -
    Real.log (1 - Real.exp (-Real.log 2 / 2))) / H

end OAI.PiExponent.DeterminantContradiction.FiniteTranslation


