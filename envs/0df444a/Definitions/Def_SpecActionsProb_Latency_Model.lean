-- Prove2me | Definitions.Def_SpecActionsProb_Latency_Model
-- name    : SpecActionsProb_Latency_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:43.073992+00:00
-- url     : https://prove2.me/theorems/e4509f09-8c67-413a-87c3-dac627e4a9f6
-- title:
--   Stochastic execution model for k-branch speculative actions
-- statement:
--   A horizon has $T$ real API calls. At each eligible window $t$, the speculator has latency $A_t\sim\mathrm{Exp}(\alpha)$, the real call has latency $B_t\sim\mathrm{Exp}(\beta)$, and each of $k$ branches independently predicts the next call correctly with probability $p$. All these primitive variables are mutually independent. A hit occurs when at least one branch succeeds.
--
--   Sequential runtime is the sum of the $T$ real-call latencies. In the Appendix A timing model, a hit at window $t$ makes steps $t$ and $t+1$ take $\min(A_t,B_t)+B_{t+1}$ and consumes the next window; a miss costs $B_t$. The last step has no window. The model also counts hits in any consecutive set of potential windows.
--
--   **Formalization Note** Windows use zero-based indices. The $\mathrm{Bernoulli}(p)$ indicators are real valued, with values $0$ and $1$. Concurrency without interference and negligible transition and parameter-construction costs are built into the runtime recurrence.
-- source:
--   Ye et al., Speculative Actions: A Lossless Framework for Faster Agentic Systems, arXiv:2510.04371v2, pp. 4–5 and 14, Assumptions 1–2, Algorithm 1, Proposition 1, Appendix A

import Mathlib
import Definitions.Def_SpecActions_model

set_option autoImplicit false

namespace SpecActionsProb.Latency

open MeasureTheory ProbabilityTheory

/-- Primitive latencies and correctness indicators. Window `t` is zero based and concerns step `t + 1`. -/
inductive Idx (k : ℕ) where
  | spec : ℕ → Idx k
  | real : ℕ → Idx k
  | branch : ℕ → Fin k → Idx k

/-- A real valued branch indicator with success probability `p`. -/
noncomputable def bernoulliReal (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac 0

/-- The independent exponential latencies and independent correctness indicators of Proposition 1. -/
structure IsSpecModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (k : ℕ) (α β p : ℝ)
    (X : Idx k → Ω → ℝ) : Prop where
  meas : ∀ j, Measurable (X j)
  indep : iIndepFun X P
  lawA : ∀ t, P.map (X (.spec t)) = expMeasure α
  lawB : ∀ t, P.map (X (.real t)) = expMeasure β
  lawG : ∀ t (i : Fin k), P.map (X (.branch t i)) = bernoulliReal p

/-- A hit means that one of the `k` branches predicts the right next call. -/
def hitAt {Ω : Type*} {k : ℕ} (X : Idx k → Ω → ℝ) (t : ℕ) (ω : Ω) : Prop :=
  ∃ i : Fin k, X (.branch t i) ω = 1

open scoped Classical in
/-- The Appendix A timing model: a hit has block time `min A B + B_next`, while a miss costs `B`.
A hit consumes the next window; the last step has no window. -/
noncomputable def specRun {Ω : Type*} {k : ℕ} (X : Idx k → Ω → ℝ) (ω : Ω) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | t, 1 => X (.real t) ω
  | t, n + 2 =>
      if hitAt X t ω then
        min (X (.spec t) ω) (X (.real t) ω) + X (.real (t + 1)) ω + specRun X ω (t + 2) n
      else X (.real t) ω + specRun X ω (t + 1) (n + 1)

noncomputable def specRuntime {Ω : Type*} {k : ℕ} (X : Idx k → Ω → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  specRun X ω 0 T

noncomputable def seqRuntime {Ω : Type*} {k : ℕ} (X : Idx k → Ω → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T, X (.real t) ω

open scoped Classical in
/-- Number of hits in `m` potential windows, with the window after a hit skipped. -/
noncomputable def hitsBy {Ω : Type*} {k : ℕ} (X : Idx k → Ω → ℝ) (ω : Ω) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | t, 1 => if hitAt X t ω then 1 else 0
  | t, m + 2 => if hitAt X t ω then 1 + hitsBy X ω (t + 2) m else hitsBy X ω (t + 1) (m + 1)

end SpecActionsProb.Latency


