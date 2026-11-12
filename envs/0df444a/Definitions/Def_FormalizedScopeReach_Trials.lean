-- Prove2me | Definitions.Def_FormalizedScopeReach_Trials
-- name    : FormalizedScopeReach_Trials
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-15T19:10:05.485335+00:00
-- url     : https://prove2.me/theorems/52e44e45-fb0e-4a99-8275-d07fdcecc6d9
-- title:
--   The two-stage Bernoulli experiment
-- statement:
--   For each outcome-free timeline, independent Bernoulli trials use the original next-token outcome probabilities along its prefixes. The joint experiment first draws an independent pool of timelines from the outcome-avoiding law and then draws the corresponding conditional trials. Its Monte Carlo average records which timelines have at least one success. The retained information consists of the entire indexed pool of outcome-free timelines. All conditional trials and the joint law are explicitly constructed, so the conditional-expectation identity is a theorem rather than a defining assumption.
-- source:
--   Solo et al., Efficient Generative Prediction for EHR Foundation Models: The SCOPE and REACH Estimators, arXiv:2602.03730v2 (2026), https://arxiv.org/abs/2602.03730v2, Appendices C and Q

import Definitions.Def_FormalizedScopeReach_Times
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace FormalizedScopeReach
variable {V : Type}

/-- Conditional independent Bernoulli trials from Appendix C. -/
def trialLaw (M : Model V) (x : Timeline V) : Measure (Fin x.length → Bool) :=
  Measure.pi (fun i : Fin x.length => bernoulliMeasure true false
    ⟨hazard M (x.take i.val), ENNReal.toReal_nonneg,
      by simpa [hazard] using (ENNReal.toReal_mono ENNReal.one_ne_top ((M.next (x.take i.val)).coe_le_one M.outcome))⟩)

instance trialLaw_probability (M : Model V) (x : Timeline V) :
    IsProbabilityMeasure (trialLaw M x) := by unfold trialLaw; infer_instance

/-- Indicator of at least one success on a fixed timeline. -/
def trialSuccess (x : Timeline V) (c : Fin x.length → Bool) : ℝ := by
  classical
  exact if c = (fun _ => false) then 0 else 1

/-- Store the finite list of trial results for a timeline. -/
def trialListLaw (M : Model V) (x : Timeline V) : Measure (List Bool) :=
  (trialLaw M x).map List.ofFn

/-- Conditional trial law for a pool of independent timelines. -/
def poolTrialLaw (M : Model V) {n : ℕ} (xs : Fin n → Timeline V) :
    Measure (Fin n → List Bool) := Measure.pi (fun i => trialListLaw M (xs i))

/-- The joint two-stage experiment: sample timelines, then their Bernoulli trials. -/
def twoStageLaw (M : Model V) [IsProbabilityMeasure (avoidingLaw M)] (n : ℕ) :
    Measure ((Fin n → Timeline V) × (Fin n → List Bool)) :=
  Measure.sum (fun xs : Fin n → Timeline V =>
    (iidLaw (avoidingLaw M) n) {xs} •
      (poolTrialLaw M xs).map (fun cs => (xs, cs)))

/-- The sampled indicator average in the paper's two-stage experiment. -/
def trialMean (n : ℕ) (z : (Fin n → Timeline V) × (Fin n → List Bool)) : ℝ := by
  classical
  exact (∑ i, if true ∈ z.2 i then (1 : ℝ) else 0) / (n : ℝ)

/-- The information retained when the outcome-free timelines are observed. -/
def timelineInformation (n : ℕ) :
    MeasurableSpace ((Fin n → Timeline V) × (Fin n → List Bool)) :=
  MeasurableSpace.comap Prod.fst inferInstance

end FormalizedScopeReach


