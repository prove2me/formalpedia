-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
-- name    : OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-17T02:56:20.292329+00:00
-- url     : https://prove2.me/theorems/c2ab0f1d-95b2-49bb-926d-9459b68c1ea0
-- title:
--   Canonical row choices and translated summands for the actual minor
-- statement:
--   Defines transverse multi-indices within the weighted simplex, finite row choices, independent choice families, the logarithmic period, period monomials, translation scalars, coefficient matrices, and their determinant summands. The scalar uses the tail truncation minus log and retains zero terms from incompatible multi-indices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

namespace OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

noncomputable def indices {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Finset (Fin d.m →₀ ℕ) :=
  (realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d)) H).map
    Finsupp.equivFunOnFinite.symm.toEmbedding

abbrev RowChoice {nu : ℝ} (d : FixedData nu) (H : ℝ) (r : Row d H) :=
  Σ a : indices d H, (∀ i : Fin d.m, Fin (a.1 i - r.2.1 i.succ + 1)) ×
    Fin (r.2.1 0 + 1)

abbrev ChoiceFamily {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ∀ r : Row d H, RowChoice d H r

noncomputable def period : ℂ := 2 * Complex.I * (Real.pi : ℂ)

noncomputable def periodMonomial {m : ℕ} (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) :=
  MvPolynomial.C ((1 + PowerSeries.X) ^ h) *
    ∏ i, (MvPolynomial.C (PowerSeries.C ((j : ℂ) * period) + PowerSeries.log ℂ) +
      MvPolynomial.X i) ^ a i

noncomputable def choiceScalar {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) : ℂ :=
  ((∏ i : Fin d.m, (t.1.1 i).choose (r.2.1 i.succ) *
    (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ) *
  (∏ i : Fin d.m,
    ((r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - period)) ^
        (t.1.1 i - r.2.1 i.succ - t.2.1 i)) *
  PowerSeries.coeff t.2.2
    (∏ i : Fin d.m,
      ((PowerSeries.trunc
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
        (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^ (t.2.1 i : ℕ))

noncomputable def choiceMatrix {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    Matrix (Row d H) (Row d H) ℂ :=
  fun r c => PowerSeries.coeff (r.2.1 0 - (f r).2.2)
    ((periodMonomial r.1.val ((selection c).1 0)
      (fun i => (selection c).1 i.succ)).coeff (f r).1.1)

noncomputable def summand {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) : ℂ :=
  (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det

end OAI.PiExponent.LiteralAnalytic.TranslatedExpansion


