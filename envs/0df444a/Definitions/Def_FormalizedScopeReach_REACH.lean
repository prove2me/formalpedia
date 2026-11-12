-- Prove2me | Definitions.Def_FormalizedScopeReach_REACH
-- name    : FormalizedScopeReach_REACH
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-15T19:09:10.588989+00:00
-- url     : https://prove2.me/theorems/b9f1d201-2803-4876-a398-455ddcd91c9a
-- title:
--   Outcome-avoiding sampling and REACH
-- statement:
--   The outcome-avoiding transitions remove the outcome token and renormalize every other token probability. The law is the sum of their product masses over outcome-free timelines ending at the same first threshold crossing. The REACH score is one minus the product of the original model non-outcome probabilities along such a timeline. The REACH estimator averages those scores. The theorem targets explicitly require this sampling law to have total mass one; this is the confirmed additional almost-sure termination and viability assumption.
-- source:
--   Solo et al., Efficient Generative Prediction for EHR Foundation Models: The SCOPE and REACH Estimators, arXiv:2602.03730v2 (2026), https://arxiv.org/abs/2602.03730v2, Sections 2.2 and 4.3; Appendix C

import Definitions.Def_FormalizedScopeReach_SCOPE

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace FormalizedScopeReach
variable {V : Type}

def avoidingStepMass (M : Model V) (h : List V) (a : V) : ℝ≥0∞ := by
  classical
  exact if a = M.outcome then 0 else M.next h a / (1 - M.next h M.outcome)

def avoidingPathMass (M : Model V) (x : Timeline V) : ℝ≥0∞ := by
  classical
  exact if terminal M x ∧ M.outcome ∉ x then
    ∏ i : Fin x.length, avoidingStepMass M (x.take i.val) (x.get i)
  else 0

def avoidingLaw (M : Model V) : Measure (Timeline V) :=
  Measure.sum (fun x => avoidingPathMass M x • Measure.dirac x)

def reachScore (M : Model V) (x : Timeline V) : ℝ :=
  1 - ∏ i : Fin x.length, (1 - hazard M (x.take i.val))

def reachEstimator (M : Model V) (n : ℕ)
    (xs : Fin n → Timeline V) : ℝ :=
  (∑ i, reachScore M (xs i)) / (n : ℝ)

end FormalizedScopeReach


