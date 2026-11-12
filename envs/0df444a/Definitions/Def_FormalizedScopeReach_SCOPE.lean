-- Prove2me | Definitions.Def_FormalizedScopeReach_SCOPE
-- name    : FormalizedScopeReach_SCOPE
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-15T19:08:14.985136+00:00
-- url     : https://prove2.me/theorems/b4cd36bb-18de-4524-8609-b0c172559aee
-- title:
--   Timeline sampling and SCOPE
-- statement:
--   The model supplies an outcome token, a next-token probability mass function for each complete history, and a prefix-based threshold predicate that is false initially. Terminal timelines end exactly at their first threshold crossing, and the original law is the sum of their next-token product masses. SCOPE sums original outcome probabilities at each position through the first outcome or the threshold, including that position. Its estimator is the average over a positive number of independently sampled original timelines. Normalization and the no-tie condition are hypotheses of the theorem targets, not assumed identities of these definitions.
-- source:
--   Solo et al., Efficient Generative Prediction for EHR Foundation Models: The SCOPE and REACH Estimators, arXiv:2602.03730v2 (2026), https://arxiv.org/abs/2602.03730v2, Sections 1.1 and 4.1; Appendix B

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace FormalizedScopeReach

structure Model (V : Type) where
  outcome : V
  next : List V → PMF V
  stop : List V → Prop
  beforeThreshold : ¬ stop []

variable {V : Type}

abbrev Timeline (V : Type) := List V

instance timelineMeasurableSpace : MeasurableSpace (Timeline V) := ⊤

instance timelineMeasurableSingletonClass : MeasurableSingletonClass (Timeline V) :=
  ⟨fun _ => trivial⟩

def active (M : Model V) (h : List V) : Prop :=
  ¬ M.stop h ∧ M.outcome ∉ h

def running (M : Model V) (h : List V) : Prop := ¬ M.stop h

def terminal (M : Model V) (x : Timeline V) : Prop :=
  M.stop x ∧ ∀ i : Fin x.length, running M (x.take i.val)

def pathMass (M : Model V) (x : Timeline V) : ℝ≥0∞ := by
  classical
  exact if terminal M x then
    ∏ i : Fin x.length, M.next (x.take i.val) (x.get i)
  else 0

def originalLaw (M : Model V) : Measure (Timeline V) :=
  Measure.sum (fun x => pathMass M x • Measure.dirac x)

def hazard (M : Model V) (h : List V) : ℝ :=
  (M.next h M.outcome).toReal

def scopeScore (M : Model V) (x : Timeline V) : ℝ := by
  classical
  exact ∑ i : Fin x.length,
    if active M (x.take i.val) then hazard M (x.take i.val) else 0

def scopeEstimator (M : Model V) (n : ℕ)
    (xs : Fin n → Timeline V) : ℝ :=
  (∑ i, scopeScore M (xs i)) / (n : ℝ)

def monteCarloScore (M : Model V) (x : Timeline V) : ℝ := by
  classical
  exact if M.outcome ∈ x then 1 else 0

def monteCarloEstimator (M : Model V) (n : ℕ)
    (xs : Fin n → Timeline V) : ℝ :=
  (∑ i, monteCarloScore M (xs i)) / (n : ℝ)

def eventProbability (M : Model V) : ℝ :=
  ((originalLaw M) {x | M.outcome ∈ x}).toReal

def iidLaw (μ : Measure (Timeline V)) [IsProbabilityMeasure μ] (n : ℕ) :
    Measure (Fin n → Timeline V) :=
  Measure.pi (fun _ : Fin n => μ)

instance iidLaw_probability (μ : Measure (Timeline V)) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (iidLaw μ n) := by unfold iidLaw; infer_instance

end FormalizedScopeReach


