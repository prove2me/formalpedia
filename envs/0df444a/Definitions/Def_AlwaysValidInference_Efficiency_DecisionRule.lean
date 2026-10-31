-- Prove2me | Definitions.Def_AlwaysValidInference_Efficiency_DecisionRule
-- name    : AlwaysValidInference_Efficiency_DecisionRule
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:38:53.092201+00:00
-- url     : https://prove2.me/theorems/72d269b1-8372-426b-bbde-6bd8a9a3329c
-- title:
--   Binary decision rules at positive stopping times
-- statement:
--   A binary decision rule consists of a sample count $T\in\{1,2,\ldots\}\cup\{\infty\}$ and a decision $\delta\in\{0,1\}$. Its observation condition relative to an increasing history $(\mathcal F_n)$ requires $\{T\le n\}\in\mathcal F_n$, a decision measurable in $\bigvee_n\mathcal F_n$, and $\{\delta=1,T\le n\}\in\mathcal F_n$ for every $n$. These are the usual stopping-time and stopped-sigma-algebra conditions for a binary decision. The parameter-law condition of not rejecting on nontermination is imposed separately by admissibility.
--
--   The generic rule has no unknown-parameter argument. Time is represented by extended natural numbers with a separate positivity condition. Its inclusion into extended nonnegative reals sends infinity to infinity and a finite count to that same count. This object can be used with any discrete observation history.
-- source:
--   Johari, Pekelis and Walsh, Always Valid Inference: Continuous Monitoring of A/B Tests, arXiv:1512.04922v3 (2019), https://arxiv.org/abs/1512.04922v3, §3, p. 11 (PDF page = printed page).

import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace AlwaysValidInference.Efficiency

/-- Generic binary decision-rule data; admissibility is stated separately. -/
structure DecisionRule (Ω : Type*) where
  time : Ω → ℕ∞
  reject : Ω → Bool

/-- Positive sample counts, stopping-time measurability, and measurability of the
decision at the stopping time. The ambient decision sigma algebra is generated
by the observation history, so no extra randomization is available. -/
def DecisionRule.Observed {Ω : Type*} (R : DecisionRule Ω)
    (F : ℕ → MeasurableSpace Ω) : Prop :=
  (∀ ω, 1 ≤ R.time ω) ∧
  (∀ n : ℕ, @MeasurableSet Ω (F n) {ω | R.time ω ≤ (n : ℕ∞)}) ∧
  @Measurable Ω Bool (⨆ n, F n) inferInstance R.reject ∧
  (∀ n : ℕ, @MeasurableSet Ω (F n)
    {ω | R.reject ω = true ∧ R.time ω ≤ (n : ℕ∞)})

/-- The order-preserving inclusion of extended natural sample counts. -/
noncomputable def timeValue (t : ℕ∞) : ℝ≥0∞ :=
  if t = ⊤ then ⊤ else (t.toNat : ℝ≥0∞)

end AlwaysValidInference.Efficiency


