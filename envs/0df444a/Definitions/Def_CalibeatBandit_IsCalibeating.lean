-- Prove2me | Definitions.Def_CalibeatBandit_IsCalibeating
-- name    : CalibeatBandit_IsCalibeating
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:34.430798+00:00
-- url     : https://prove2.me/theorems/246f20cd-c387-40d2-a4ec-d90545a58c54
-- title:
--   $(\alpha,\beta)$-calibeating (Definition 2.2)
-- statement:
--   Fix $\alpha,\beta$. A learner is **$(\alpha,\beta)$-calibeating over $T$ rounds** if, for every recommendation and reward sequence satisfying the interaction protocol,
--   $$\mathbb E[\mathrm{SR}_T]\le\alpha T,\qquad \mathbb E[\mathrm{Rec}_T]\le\beta T .$$
--
--   **Formalization Note** "Every recommendation and reward sequence satisfying the interaction protocol" is every run of the protocol (`ProtocolRun`) on every probability space in a fixed universe; $\mathbb E$ is the Bochner integral. The paper's standing $\alpha,\beta\ge0$ is not needed for the definition.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Definition 2.2, p.8 (PDF 8)

import Mathlib
import Definitions.Def_CalibeatBandit_ProtocolRun
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_rewardLoss

set_option autoImplicit false

universe u

namespace CalibeatBandit

open MeasureTheory

/-- **(α, β)-calibeating (Definition 2.2).** A learner is `(α, β)`-calibeating over `T` rounds
if, for every recommendation and reward sequence satisfying the interaction protocol,
`E[SR_T] ≤ αT` and `E[Rec_T] ≤ βT`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Definition 2.2,
p.8.

**Formalization Note.** "Every recommendation and reward sequence satisfying the interaction
protocol" is every `ProtocolRun` on every probability space `(Ω, P)` with `Ω` in a fixed
universe `u`; `E` is the Bochner integral, and `SR_T`, `Rec_T` are bounded measurable random
variables in every run, so the integrals are genuine. The paper's standing `α, β ≥ 0` is not
needed for the definition. -/
def IsCalibeating (K T : ℕ) (α β : ℝ) (policy : Policy K) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : ProtocolRun K T P policy),
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P ≤ α * T ∧
    ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P ≤ β * T

end CalibeatBandit


