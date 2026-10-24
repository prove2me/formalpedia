-- Prove2me | Definitions.Def_OAI_PiExponent_MinorTranslationData
-- name    : OAI_PiExponent_MinorTranslationData
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-23T22:57:49.679453+00:00
-- url     : https://prove2.me/theorems/2fdc018d-a329-4dd4-b0fe-7b01a931a2fa
-- title:
--   Finite translation choices, scalars, period matrices, and collision data
-- statement:
--   A definition-only interface for the source translation argument, reusing the existing FixedData, row/column types, weighted simplices, and truncated-log definitions. Each row choice contains a transverse index, bounded tail exponents, and a coefficient order k≤s. The scalar uses the signed truncation tail; the matrix uses full-log coefficients at the formal period. Multiplicity records the number of rows sharing an index. The remainder and translation count are exactly the explicit quantities in the target.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators
noncomputable section

namespace OAI.PiExponent.MinorTranslationData
open DeterminantContradiction

-- Definition-only port of the finite translation interface at
-- openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a:
-- RowTranslation, MatrixTranslation, and LiteralAnalyticSummand.
def fixedWeights {nu : ℝ} (d : FixedData nu) : Fin d.m → ℝ :=
  MatrixArithmetic.logWeights (finiteDenominators d)

def transverseIndices {m : ℕ} (w : Fin m → ℝ) (H : ℝ) :
    Finset (Fin m →₀ ℕ) :=
  (realWeightedSimplex w H).map Finsupp.equivFunOnFinite.symm.toEmbedding

abbrev Transverse {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ↥(transverseIndices (fixedWeights d) H)

def beta {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) : Fin d.m →₀ ℕ :=
  InterpolationMatrix.exponentVector (fun i => r.2.1 i.succ)

abbrev RowChoice {nu : ℝ} (d : FixedData nu) (H : ℝ) (r : Row d H) :=
  Σ a : Transverse d H, (∀ i, Fin (a.1 i - beta d r i + 1)) × Fin (r.2.1 0 + 1)

abbrev ChoiceFamily {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ∀ r : Row d H, RowChoice d H r

def indexWeight {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Transverse d H) : ℝ :=
  ∑ i, fixedWeights d i * (a.1 i : ℝ)

def rowWeight {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) : ℝ :=
  ∑ i, fixedWeights d i * (beta d r i : ℝ)

def period : ℂ := 2 * (Real.pi : ℂ) * Complex.I

def tail (T : ℕ) : PowerSeries ℂ :=
  (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ

def choiceScalar {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) : ℂ :=
  ((∏ i, (t.1.1 i).choose (beta d r i) *
    (t.1.1 i - beta d r i).choose (t.2.1 i) : ℕ) : ℂ) *
  (∏ i, ((r.1.val : ℂ) *
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - period)) ^
      (t.1.1 i - beta d r i - t.2.1 i)) *
  PowerSeries.coeff (t.2.2 : ℕ)
    (∏ i, tail (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) ^
      (t.2.1 i : ℕ))

def periodMonomial {m : ℕ} (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) :=
  MvPolynomial.C ((1 + PowerSeries.X) ^ h) *
    ∏ i, (MvPolynomial.C (PowerSeries.C ((j : ℂ) * period) + PowerSeries.log ℂ) +
      MvPolynomial.X i) ^ a i

def choiceMatrix {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    Matrix (Row d H) (Row d H) ℂ :=
  fun r c => PowerSeries.coeff (r.2.1 0 - (f r).2.2)
    ((periodMonomial r.1.val ((selection c).1 0)
      (fun i => (selection c).1 i.succ)).coeff (f r).1.1)

def multiplicity {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (group : ι → κ) (a : κ) : ℕ :=
  (Finset.univ.filter fun i => group i = a).card

def remainder (M : ℕ) (H : ℝ) : ℝ :=
  (Real.log (M : ℝ) + Real.log 2 / 4 -
    Real.log (1 - Real.exp (-Real.log 2 / 2))) / H

def termCount (m : ℕ) (v H : ℝ) : ℕ :=
  (⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v⌋₊ + 1)

end OAI.PiExponent.MinorTranslationData


