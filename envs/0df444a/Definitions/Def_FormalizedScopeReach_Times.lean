-- Prove2me | Definitions.Def_FormalizedScopeReach_Times
-- name    : FormalizedScopeReach_Times
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-15T19:09:44.727714+00:00
-- url     : https://prove2.me/theorems/cf237ebc-2552-48e3-85e4-f16cc74ae4f0
-- title:
--   Stopping times and the three estimators
-- statement:
--   The first outcome time is the first one-based token position occupied by the outcome, or infinity if it does not occur. The threshold time is the first prefix length at which the threshold predicate holds, or infinity if it never holds within the list. The model rules out crossing at the empty prefix. Monte Carlo averages the indicators of the strict event that the first outcome precedes that threshold. The definitions also expose SCOPE and REACH under their paper symbols, and specify the original target probability. The threshold time is not reassigned after an outcome.
-- source:
--   Solo et al., Efficient Generative Prediction for EHR Foundation Models: The SCOPE and REACH Estimators, arXiv:2602.03730v2 (2026), https://arxiv.org/abs/2602.03730v2, Section 1.1; Appendix B; user-specified actual threshold crossing

import Definitions.Def_FormalizedScopeReach_REACH
import Mathlib.Data.ENat.Basic

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace FormalizedScopeReach
variable {V : Type}

/-- First occurrence of the outcome, using the paper's indices 1, 2, ... . -/
def T_O (M : Model V) (x : Timeline V) : ℕ∞ := by
  classical
  exact if M.outcome ∈ x then (x.idxOf M.outcome + 1 : ℕ) else ⊤

/-- First prefix that exceeds the time threshold. All prefix tokens may be used. -/
def T_E (M : Model V) (x : Timeline V) : ℕ∞ := by
  classical
  exact if h : ∃ n : ℕ, n ≤ x.length ∧ M.stop (x.take n) then
    (Nat.find h : ℕ) else ⊤

/-- The paper's Monte Carlo estimator M₀, on n sampled timelines. -/
def M₀ (M : Model V) (n : ℕ) (xs : Fin n → Timeline V) : ℝ := by
  classical
  exact (∑ i, if T_O M (xs i) < T_E M (xs i) then (1 : ℝ) else 0) / (n : ℝ)

/-- The SCOPE estimator 𝒮. -/
def 𝒮 (M : Model V) (n : ℕ) (xs : Fin n → Timeline V) : ℝ :=
  scopeEstimator M n xs

/-- The REACH estimator ℛ, evaluated on outcome-avoiding timelines. -/
def ℛ (M : Model V) (n : ℕ) (xs : Fin n → Timeline V) : ℝ :=
  reachEstimator M n xs

/-- Probability to be estimated: the first outcome precedes the time threshold. -/
def targetProbability (M : Model V) : ℝ :=
  ((originalLaw M) {x | T_O M x < T_E M x}).toReal

end FormalizedScopeReach


