-- Prove2me | Definitions.Def_PiExponent_FiniteTranslationData_690acb6f
-- name    : PiExponent_FiniteTranslationData_690acb6f
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-24T09:27:08.502246+00:00
-- url     : https://prove2.me/theorems/c54a7395-06bb-4884-b678-2bc6bf67ac41
-- title:
--   Finite data for literal translated minors
-- statement:
--   Finite-data versions of the literal translated-minor terms, built from the target’s existing interpolation matrix, simplex, and arithmetic definitions. The helper namespace and bundle name are unique to this candidate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Ring.Basic

open scoped BigOperators

namespace OAI.PiExponent.FiniteMinorAnalysis_690acb6f

abbrev Rows {m : ℕ} (K : ℕ) (v theta : ℝ) (q : Fin m → ℕ) (H : ℝ) :=
  InterpolationMatrix.Row K v theta (MatrixArithmetic.logWeights q) H

abbrev Columns {m : ℕ} (w0 : ℝ) (q : Fin m → ℕ) (H : ℝ) :=
  InterpolationMatrix.Column w0 (MatrixArithmetic.logWeights q) H

noncomputable def transverseIndices {m : ℕ} (q : Fin m → ℕ) (H : ℝ) :
    Finset (Fin m →₀ ℕ) :=
  (realWeightedSimplex (MatrixArithmetic.logWeights q) H).map
    Finsupp.equivFunOnFinite.symm.toEmbedding

abbrev Transverse {m : ℕ} (q : Fin m → ℕ) (H : ℝ) :=
  ↥(transverseIndices q H)

noncomputable def weight {m : ℕ} (q : Fin m → ℕ) (a : Fin m →₀ ℕ) : ℝ :=
  ∑ i, MatrixArithmetic.logWeights q i * (a i : ℝ)

noncomputable def beta {m : ℕ} {K : ℕ} {v theta H : ℝ}
    {q : Fin m → ℕ} (r : Rows K v theta q H) : Fin m →₀ ℕ :=
  InterpolationMatrix.exponentVector (fun i => r.2.1 i.succ)

abbrev RowChoice {m : ℕ} {K : ℕ} {v theta H : ℝ}
    {q : Fin m → ℕ} (r : Rows K v theta q H) :=
  Σ a : Transverse q H, (∀ i : Fin m, Fin (a.1 i - beta r i + 1)) ×
    Fin (r.2.1 0 + 1)

abbrev Choices {m : ℕ} (K : ℕ) (v theta : ℝ) (q : Fin m → ℕ) (H : ℝ) :=
  ∀ r : Rows K v theta q H, RowChoice r

noncomputable def period : ℂ := 2 * (Real.pi : ℂ) * Complex.I

noncomputable def periodMonomial {m : ℕ} (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) :=
  MvPolynomial.C ((1 + PowerSeries.X) ^ h) *
    ∏ i, (MvPolynomial.C (PowerSeries.C ((j : ℂ) * period) +
      PowerSeries.log ℂ) + MvPolynomial.X i) ^ a i

noncomputable def logTail (T : ℕ) : PowerSeries ℂ :=
  (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ

noncomputable def scalar {m : ℕ} {K : ℕ} {v theta H : ℝ}
    (F : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (r : Rows K v theta q H) (t : RowChoice r) : ℂ :=
  ((∏ i, (t.1.1 i).choose (beta r i) *
      (t.1.1 i - beta r i).choose (t.2.1 i) : ℕ) : ℂ) *
    (∏ i, ((r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters p q i - period)) ^
        (t.1.1 i - beta r i - t.2.1 i)) *
    PowerSeries.coeff (t.2.2 : ℕ)
      (∏ i, logTail (MatrixArithmetic.truncationOrders q F v i) ^ (t.2.1 i : ℕ))

noncomputable def periodMatrix {m : ℕ} {K : ℕ} {w0 v theta H : ℝ}
    {q : Fin m → ℕ} (selection : Rows K v theta q H → Columns w0 q H)
    (f : Choices K v theta q H) : Matrix (Rows K v theta q H) (Rows K v theta q H) ℂ :=
  fun r c => PowerSeries.coeff (r.2.1 0 - ((f r).2.2 : ℕ))
    ((periodMonomial r.1.val ((selection c).1 0)
      (fun i => (selection c).1 i.succ)).coeff (f r).1.1)

noncomputable def rowCount {m : ℕ} (K : ℕ) (v theta : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℕ := Fintype.card (Rows K v theta q H)

noncomputable def termCount (m : ℕ) (v H : ℝ) : ℕ :=
  (⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v⌋₊ + 1)

noncomputable def lowCount {m : ℕ} (q : Fin m → ℕ) (A H : ℝ) : ℕ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights q) (A * H)).card

noncomputable def multiplicity {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (group : ι → κ) (a : κ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => group i = a)).card

noncomputable def collisionRemainder (M : ℕ) (H : ℝ) : ℝ :=
  (Real.log (M : ℝ) + Real.log 2 / 4 -
    Real.log (1 - Real.exp (-Real.log 2 / 2))) / H

noncomputable def remainder {m : ℕ} (K : ℕ) (v theta : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  collisionRemainder (rowCount K v theta q H) H +
    Real.log (termCount m v H : ℝ) / H

noncomputable def translationError (K : ℕ) (nu F v wmin : ℝ) : ℝ :=
  nu / F + Real.log 2 / v + (Real.log 4 + Real.log (2 * (K : ℝ)) + nu) / wmin

noncomputable def holomorphicError (K : ℕ) (w0 v wmin : ℝ) : ℝ :=
  100 * (K : ℝ) / w0 + Real.log 2 / v + Real.log (200 * (K : ℝ)) / wmin

end OAI.PiExponent.FiniteMinorAnalysis_690acb6f


