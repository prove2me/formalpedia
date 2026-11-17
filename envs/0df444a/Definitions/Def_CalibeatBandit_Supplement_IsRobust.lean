-- Prove2me | Definitions.Def_CalibeatBandit_Supplement_IsRobust
-- name    : CalibeatBandit_Supplement_IsRobust
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:27:59.930188+00:00
-- url     : https://prove2.me/theorems/92876181-fd8f-48ec-8a1d-bebe9c3741ea
-- title:
--   Definition 3.3 — $(\alpha,\beta,\gamma)$-robust calibeating with thresholds $\{C_s\}$
-- statement:
--   Fix $\alpha,\beta,\gamma$ and a sequence $\{C_s\}_{s=1}^T$. The **prefix swap regret of the recommendation** after $s$ rounds is
--   $$\mathrm{SR}^{\mathrm{Rec}}_s=\max_{\sigma:\mathcal A\to\mathcal A}\sum_{t=1}^s\big(y_t(\sigma(J_t))-y_t(J_t)\big).$$
--   A learner is **$(\alpha,\beta,\gamma)$-robust with $\{C_s\}_{s=1}^T$** if, for every recommendation and reward sequence satisfying the interaction protocol,
--
--   1. the learner is $(\alpha,\beta)$-calibeating, and
--   2. whenever the recommendation has low prefix swap regret with high probability,
--   $$\mathbb P\big[\mathrm{SR}^{\mathrm{Rec}}_s\le sC_s\ \text{for }1\le s\le T\big]\ge1-\rho\qquad(3.4)$$
--   for some $\rho\in[0,1]$, the learner satisfies
--   $$\mathbb E[\mathrm{SR}_T]\le\mathbb E\big[\mathrm{SR}^{\mathrm{Rec}}_T\big]+(\rho+\gamma)T,\qquad \mathbb E[\mathrm{Rec}_T]\le\mathbb E\big[\mathrm{SR}^{\mathrm{Rec}}_T\big]+(\rho+\gamma)T.$$
--
--   The first condition is a worst-case guarantee. The second is a consistency guarantee: when the recommendation already has low prefix swap regret, the learner loses little relative to it.
--
--   **Formalization Note** Clause 2 is required of every run and every $\rho\in[0,1]$ satisfying (3.4), which is the meaning of "for some $\rho$" here. $C_s$ is read for $1\le s\le T$. $\mathrm{SR}^{\mathrm{Rec}}_s$ is the base `swapRegret s y J` of the realized recommended actions.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Definition 3.3 and the display before it, p.11 (PDF 11)

import Mathlib
import Definitions.Def_CalibeatBandit_Supplement_IsQCalibeating

set_option autoImplicit false

universe u

namespace CalibeatBandit

namespace Supplement

open MeasureTheory

/-- **Robust calibeating (Definition 3.3).** Fix `α, β, γ ≥ 0` and thresholds `{C_s}_{s=1}^T`.
A learner is `(α, β, γ)`-robust with `{C_s}` if, for every recommendation and reward sequence
satisfying the interaction protocol,
1. the learner is `(α, β)`-calibeating, and
2. if the recommendation has low prefix swap regret with high probability,
   `P[SR^Rec_s ≤ s C_s for 1 ≤ s ≤ T] ≥ 1 − ρ` (3.4) for some `ρ ∈ [0, 1]`, then
   `E[SR_T] ≤ E[SR^Rec_T] + (ρ + γ)T` and `E[Rec_T] ≤ E[SR^Rec_T] + (ρ + γ)T`.

Here `SR^Rec_s = max_σ ∑_{t=1}^s (y_t(σ(J_t)) − y_t(J_t))` is the recommendation's prefix swap
regret (p.11), i.e. the base `swapRegret s y J` of the realized recommended actions.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Definition 3.3
and the display before it, p.11.

**Formalization Note.** Clause 1 is `IsQCalibeating` (it quantifies over every run, as the
paper's "for every … sequence … the learner is (α, β)-calibeating" does). Clause 2 quantifies
over every run of the protocol on every probability space with `Ω : Type u` and every
`ρ ∈ [0, 1]` satisfying (3.4). `C s` is read for `1 ≤ s ≤ T` (the paper's 1-indexed `s`);
`swapRegret s` sums the first `s` rounds. The paper's standing `α, β, γ ≥ 0` is not needed for
the definition. -/
def IsRobust (K T : ℕ) (α β γ : ℝ) (C : ℕ → ℝ) (policy : QPolicy K) : Prop :=
  IsQCalibeating.{u} K T α β policy ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : QProtocolRun K T P policy) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
    ENNReal.ofReal (1 - ρ) ≤
      P {ω | ∀ s : ℕ, 1 ≤ s → s ≤ T →
        swapRegret s (fun t => run.y t ω) (fun t => run.J t ω) ≤ s * C s} →
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
        ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P + (ρ + γ) * T ∧
    ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
        ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.J t ω) ∂P + (ρ + γ) * T

end Supplement

end CalibeatBandit


