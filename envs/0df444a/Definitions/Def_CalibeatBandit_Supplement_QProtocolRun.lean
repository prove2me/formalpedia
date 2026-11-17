-- Prove2me | Definitions.Def_CalibeatBandit_Supplement_QProtocolRun
-- name    : CalibeatBandit_Supplement_QProtocolRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:26:44.157196+00:00
-- url     : https://prove2.me/theorems/1b82e3d6-b138-447b-8a33-5b01fec77387
-- title:
--   The interaction protocol of §2.1 for learners that read the recommendation $q_t$
-- statement:
--   Fix $K$ actions $\mathcal A=[K]$ and a horizon of $T$ rounds. A **learner that reads the recommendation** chooses, in round $t$, a mixed strategy $p_t\in\Delta(\mathcal A)$ as a function of the recommended mixed strategies $q_1,\dots,q_t$, the recommended actions $J_1,\dots,J_t$, its own past actions $I_1,\dots,I_{t-1}$ and the observed rewards $y_1(I_1),\dots,y_{t-1}(I_{t-1})$. It sees nothing of the current or future rounds beyond $q_t$ and $J_t$.
--
--   A **run of the interaction protocol** on a probability space $(\Omega,\mathcal F,\mathbb P)$ consists of a growing family of sub-$\sigma$-algebras $\mathcal I_t\subseteq\mathcal F$ (everything fixed before the learner's fresh randomness of round $t$) and random variables $q_t,y_t,J_t,I_t$ such that, for every round $t$:
--
--   1. $q_t\in\Delta(\mathcal A)$ and $y_t\in[0,1]^K$ are $\mathcal I_t$-measurable (non-anticipation);
--   2. $J_t$ is drawn from $q_t$: $\mathbb P[J_t=j\mid\mathcal I_t]=q_t(j)$ almost surely;
--   3. $I_t$ is drawn from the learner's mixed strategy: $\mathbb P[I_t=i\mid\mathcal I_t\vee\sigma(J_t)]=p_t(i)$ almost surely;
--   4. $J_t$ and $I_t$ are $\mathcal I_{t+1}$-measurable.
--
--   Both $q_t$ and $y_t$ may depend on the past and may be correlated through information the learner never sees; the learner only observes $y_t(I_t)$ (bandit feedback).
--
--   This is the protocol of the base mission's `CalibeatBandit.ProtocolRun`, field for field. The only change is that the learner's input now includes $q_t$, which Algorithm 2 and the lower bound of Theorem 3.6 need.
--
--   **Formalization Note** Rounds are $0,\dots,T-1$ and actions are `Fin K`. The learner's inputs are prefixes indexed by `Fin (t+1)` and `Fin t`, so a learner cannot read the future. The draws are stated as conditional expectations of indicators.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §2.1 (Interaction protocol), p.7 (PDF 7); Algorithm 2, p.12 (PDF 12)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

namespace Supplement

open MeasureTheory

/-- A **bandit-feedback learner that reads the recommendation** (`K` actions). In round `t`
(rounds `0, 1, …`) it receives
* the recommended mixed strategies `q_0, …, q_t` (as vectors `Fin K → ℝ`),
* the recommended actions `J_0, …, J_t`,
* its own past actions `I_0, …, I_{t−1}`,
* the observed rewards `r_0, …, r_{t−1}`, where `r_s = y_s(I_s)`,
and returns its mixed strategy `p_t` for round `t`, as a vector `Fin K → ℝ`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §2.1
"Interaction protocol", p.7, item 3: "The learner has access to the recommendation q_t and the
feedback from previous rounds. She selects a mixed strategy p_t ∈ Δ(𝒜)". Algorithm 2 (p.12) reads
`q_t` itself (`p_t = (1 − ε)q_t + εu`, `Ĝ` uses `q_t(i)`).

**Formalization Note.** The inputs are prefixes indexed by `Fin (t + 1)` and `Fin t`, so a
learner cannot read future rounds, the current action or the current reward. The base mission's
`CalibeatBandit.Policy` receives only `J`; this type adds `q`. -/
abbrev QPolicy (K : ℕ) : Type :=
  (t : ℕ) → (Fin (t + 1) → Fin K → ℝ) → (Fin (t + 1) → Fin K) → (Fin t → Fin K) → (Fin t → ℝ) →
    Fin K → ℝ

/-- **A run of the `T`-round interaction protocol of §2.1 driven by a learner that reads the
recommendation**, on a probability space `(Ω, P)`. Field for field the same as the base
mission's `CalibeatBandit.ProtocolRun`; only the learner's inputs in `I_law` differ.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §2.1
"Interaction protocol", p.7: in each round `t`, (1) the recommendation algorithm gives
`q_t ∈ Δ(𝒜)`; (2) the adversary chooses `y_t ∈ [0,1]^K`, not yet revealed; (3) the learner, who
has access to `q_t` and the feedback from previous rounds, selects `p_t ∈ Δ(𝒜)`, draws `I_t ∼ p_t`;
`J_t ∼ q_t` is the action of the recommendation algorithm; (4) the learner receives `y_t(I_t)`.
"Both q_t and y_t may depend on the past interaction, and they may be correlated through
information unavailable to the learner. We impose only a non-anticipation condition. That is,
they are chosen before the learner draws any fresh randomness in round t."

Fields:
* `info t`: everything fixed before the learner's round-`t` draws (the whole past, the
  environment's private information, `q_t` and `y_t`); a growing family of sub-σ-algebras;
* `q t`, `y t`: `info t`-measurable, `q_t ∈ Δ(𝒜)`, `y_t ∈ [0,1]^K`;
* `J t`: `P[J_t = j | info t] = q_t(j)` a.s.;
* `I t`: `P[I_t = i | info t ∨ σ(J_t)] = p_t(i)` a.s., where `p_t` is `policy t` applied to
  `q_0, …, q_t`, `J_0, …, J_t`, `I_0, …, I_{t−1}` and the observed rewards `y_s(I_s)`, `s < t`.

**Formalization Note.** Rounds are `0, …, T − 1`; actions are `Fin K` with the discrete
σ-algebra. The draws are stated through conditional expectations of indicators, so the
environment may be adaptive, randomized and correlated with the recommendation through
information the learner never sees. As in the base protocol, the learner sees the drawn `J_t`
(Algorithm 1, p.10, and Algorithm 2, p.12, draw `J_t ∼ q_t` themselves). -/
structure QProtocolRun (K T : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (policy : QPolicy K) where
  /-- information available before the learner's draws in round `t` -/
  info : ℕ → MeasurableSpace Ω
  /-- recommended mixed strategy `q_t` -/
  q : ℕ → Ω → Fin K → ℝ
  /-- reward vector `y_t` -/
  y : ℕ → Ω → Fin K → ℝ
  /-- recommended action `J_t ∼ q_t` -/
  J : ℕ → Ω → Fin K
  /-- played action `I_t ∼ p_t` -/
  I : ℕ → Ω → Fin K
  info_le : ∀ t ≤ T, info t ≤ mΩ
  info_mono : ∀ t < T, info t ≤ info (t + 1)
  q_measurable : ∀ t < T, Measurable[info t] (q t)
  y_measurable : ∀ t < T, Measurable[info t] (y t)
  J_measurable : ∀ t < T, Measurable[info (t + 1)] (J t)
  I_measurable : ∀ t < T, Measurable[info (t + 1)] (I t)
  q_nonneg : ∀ t < T, ∀ ω i, 0 ≤ q t ω i
  q_sum : ∀ t < T, ∀ ω, ∑ i, q t ω i = 1
  y_mem : ∀ t < T, ∀ ω i, y t ω i ∈ Set.Icc (0 : ℝ) 1
  J_law : ∀ t < T, ∀ j : Fin K,
    condExp (info t) P ((J t ⁻¹' {j}).indicator (fun _ => (1 : ℝ))) =ᵐ[P] fun ω => q t ω j
  I_law : ∀ t < T, ∀ i : Fin K,
    condExp (info t ⊔ MeasurableSpace.comap (J t) inferInstance) P
        ((I t ⁻¹' {i}).indicator (fun _ => (1 : ℝ)))
      =ᵐ[P] fun ω => policy t (fun s => q s ω) (fun s => J s ω) (fun s => I s ω)
          (fun s => y s ω (I s ω)) i

end Supplement

end CalibeatBandit


