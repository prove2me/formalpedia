-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
-- name    : OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-11T20:56:22.981518+00:00
-- url     : https://prove2.me/theorems/20a36293-ad9b-41de-b2a1-463e0f7f0094
-- title:
--   Original literal analytic row choices and summand data
-- statement:
--   For the original admissible fixed data $d$, height $H$, row $r$, and column selection, define the finite transverse indices, row choices and choice families used in the literal determinant expansion. The weights are $w=\log q$, $\operatorname{wt}_w(a)=\sum_i w_i a_i$, and the logarithmic period is $\omega=2\pi i$. Define the period series $j\omega+\log(1+X)$, translated monomials, the truncation tail and the original binomial row scalar. The functions $\beta$, rowWeight, indexWeight, choiceScalar and choiceMatrix retain exactly their original source types and formulas. These seventeen definitions state the immediate analytic-minor and summand-bound interfaces; this package asserts no estimate, limit or determinant theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L12-L47

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


namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

noncomputable def beta {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) : Fin d.m →₀ ℕ :=
  InterpolationMatrix.exponentVector (fun i => r.2.1 i.succ)

end OAI.PiExponent.LiteralAnalytic

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

noncomputable def fixedWeights {nu : ℝ} (d : FixedData nu) : Fin d.m → ℝ :=
  MatrixArithmetic.logWeights (finiteDenominators d)

end OAI.PiExponent.LiteralAnalytic

namespace OAI.PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

noncomputable def periodCoordinate (j : ℕ) (ω : ℂ) : PowerSeries ℂ :=
  PowerSeries.C ((j : ℂ) * ω) + PowerSeries.log ℂ

end OAI.PiExponent.MatrixTranslation

namespace OAI.PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

noncomputable def transverseIndices {m : ℕ} (w : Fin m → ℝ) (H : ℝ) :
    Finset (Fin m →₀ ℕ) :=
  (PiExponent.realWeightedSimplex w H).map Finsupp.equivFunOnFinite.symm.toEmbedding

end OAI.PiExponent.MatrixTranslation

namespace OAI.PiExponent.MatrixTranslationBounds

open scoped BigOperators
open RowTranslation

noncomputable def weight {σ : Type*} [Fintype σ] (w : σ → ℝ) (a : σ → ℕ) : ℝ :=
  ∑ i, w i * a i

end OAI.PiExponent.MatrixTranslationBounds

namespace OAI.PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

abbrev RowChoices (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s : ℕ) :=
  Σ a : S, (∀ i, Fin (a.1 i - β i + 1)) × Fin (s + 1)

end OAI.PiExponent.RowTranslation

namespace OAI.PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

noncomputable def rowScalar (ε : σ → R) (τ : σ → PowerSeries R)
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) : R :=
  ((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : R) *
    (∏ i, ε i ^ (a i - β i - d i)) *
      PowerSeries.coeff k (∏ i, τ i ^ (d i : ℕ))

end OAI.PiExponent.RowTranslation

namespace OAI.PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial
variable {R : Type*} [CommRing R]

noncomputable def tail (T : ℕ) (f : PowerSeries R) : PowerSeries R :=
  (PowerSeries.trunc T f : PowerSeries R) - f

end OAI.PiExponent.RowTranslation

namespace OAI.PiExponent



noncomputable def logarithmicPeriod : ℂ := 2 * (Real.pi : ℂ) * Complex.I

end OAI.PiExponent

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

abbrev RowChoice {nu : ℝ} (d : FixedData nu) (H : ℝ) (r : Row d H) :=
  RowTranslation.RowChoices (MatrixTranslation.transverseIndices (fixedWeights d) H)
    (beta d r) (r.2.1 0)

end OAI.PiExponent.LiteralAnalytic

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

abbrev Transverse {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ↥(MatrixTranslation.transverseIndices (fixedWeights d) H)

end OAI.PiExponent.LiteralAnalytic

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

noncomputable def rowWeight {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) : ℝ :=
  MatrixTranslationBounds.weight (fixedWeights d) (fun i => beta d r i)

end OAI.PiExponent.LiteralAnalytic

namespace OAI.PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

noncomputable def periodMonomial {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) : MvPolynomial (Fin m) (PowerSeries ℂ) :=
  C ((1 + PowerSeries.X) ^ h) *
    ∏ i, (C (periodCoordinate j ω) + X i) ^ a i

end OAI.PiExponent.MatrixTranslation

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

abbrev ChoiceFamily {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ∀ r : Row d H, RowChoice d H r

end OAI.PiExponent.LiteralAnalytic

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

noncomputable def choiceScalar {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) : ℂ :=
  RowTranslation.rowScalar
    (fun i => (r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - logarithmicPeriod))
    (fun i => RowTranslation.tail
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) (PowerSeries.log ℂ))
    (beta d r) t.1.1 t.2.1 t.2.2

end OAI.PiExponent.LiteralAnalytic

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

noncomputable def indexWeight {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Transverse d H) : ℝ :=
  MatrixTranslationBounds.weight (fixedWeights d) (fun i => a.1 i)

end OAI.PiExponent.LiteralAnalytic

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators
open DeterminantContradiction

noncomputable def choiceMatrix {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) : Matrix (Row d H) (Row d H) ℂ :=
  fun r c => PowerSeries.coeff (r.2.1 0 - (f r).2.2)
    ((MatrixTranslation.periodMonomial r.1.val logarithmicPeriod
      ((selection c).1 0) (fun i => (selection c).1 i.succ)).coeff (f r).1.1)

end OAI.PiExponent.LiteralAnalytic


