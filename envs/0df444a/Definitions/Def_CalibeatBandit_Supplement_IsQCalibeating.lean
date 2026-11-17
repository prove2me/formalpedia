-- Prove2me | Definitions.Def_CalibeatBandit_Supplement_IsQCalibeating
-- name    : CalibeatBandit_Supplement_IsQCalibeating
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:27:24.045062+00:00
-- url     : https://prove2.me/theorems/2c19461d-9644-4990-b5ad-dbac30a61ec7
-- title:
--   $(\alpha,\beta)$-calibeating (Definition 2.2) for learners that read $q_t$
-- statement:
--   Fix $\alpha,\beta$. A learner that reads the recommendation is **$(\alpha,\beta)$-calibeating over $T$ rounds** if, for every recommendation and reward sequence satisfying the interaction protocol of §2.1,
--   $$\mathbb E[\mathrm{SR}_T]\le\alpha T,\qquad \mathbb E[\mathrm{Rec}_T]\le\beta T,$$
--   where $\mathrm{SR}_T=\max_{\sigma:\mathcal A\to\mathcal A}\sum_{t=1}^T\big(y_t(\sigma(I_t))-y_t(I_t)\big)$ is the learner's swap regret and $\mathrm{Rec}_T=\max_{\sigma}\sum_{t=1}^T\big(y_t(\sigma(J_t))-y_t(I_t)\big)$ is its reward loss against the best post-processing of the recommended actions.
--
--   This is the base mission's `CalibeatBandit.IsCalibeating`, restated for learners that read $q_t$. The robust learner of Algorithm 2 needs it.
--
--   **Formalization Note** "Every recommendation and reward sequence" means every run (`QProtocolRun`) on every probability space whose sample space lies in a fixed universe. $\mathrm{SR}_T$ and $\mathrm{Rec}_T$ are the base mission's `swapRegret` and `rewardLoss`, and the expectation is the Bochner integral (both are bounded and measurable in every run).
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Definition 2.2, p.8 (PDF 8)

import Mathlib
import Definitions.Def_CalibeatBandit_Supplement_QProtocolRun
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_rewardLoss

set_option autoImplicit false

universe u

namespace CalibeatBandit

namespace Supplement

open MeasureTheory

/-- **(α, β)-calibeating (Definition 2.2) for learners that read the recommendation.** A learner
is `(α, β)`-calibeating over `T` rounds if, for every recommendation and reward sequence
satisfying the interaction protocol, `E[SR_T] ≤ αT` and `E[Rec_T] ≤ βT`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Definition 2.2,
p.8.

**Formalization Note.** The same predicate as the base mission's `CalibeatBandit.IsCalibeating`,
for a `QPolicy`: "every recommendation and reward sequence satisfying the interaction protocol"
is every `QProtocolRun` on every probability space `(Ω, P)` with `Ω : Type u`; `SR_T` and
`Rec_T` are the base `swapRegret` and `rewardLoss` of the realized sequences, and `E` is the
Bochner integral (both are bounded measurable random variables in every run). -/
def IsQCalibeating (K T : ℕ) (α β : ℝ) (policy : QPolicy K) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : QProtocolRun K T P policy),
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P ≤ α * T ∧
    ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P ≤ β * T

end Supplement

end CalibeatBandit


