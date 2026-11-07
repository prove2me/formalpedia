-- Prove2me | Definitions.Def_CalibeatBandit_ProtocolRun
-- name    : CalibeatBandit_ProtocolRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:43.741444+00:00
-- url     : https://prove2.me/theorems/e3dd6ce5-b240-4c57-9e4d-aa8054545507
-- title:
--   A run of the §2.1 interaction protocol driven by a bandit-feedback learner
-- statement:
--   A **bandit-feedback learner** (policy) maps, in round $t$, the recommended actions $J$, its own past actions $I$ and the observed rewards $r_s=y_s(I_s)$ to a mixed strategy $p_t$.
--
--   A **run of the interaction protocol** over $T$ rounds, on a probability space $(\Omega,\mathcal F,P)$, driven by a policy, consists of
--   1. σ-algebras $\mathcal E_0\subseteq\mathcal E_1\subseteq\cdots\subseteq\mathcal F$, where $\mathcal E_t$ is everything fixed before the learner's random draws of round $t$ (the past interaction, any private information of the environment, $q_t$ and $y_t$);
--   2. recommendations $q_t\in\Delta(\mathcal A)$ and reward vectors $y_t\in[0,1]^K$, both $\mathcal E_t$-measurable (non-anticipation): they may depend on the past and be correlated through information unavailable to the learner;
--   3. a recommended action $J_t$ with $P(J_t=j\mid\mathcal E_t)=q_t(j)$ a.s., and a played action $I_t$ with $P(I_t=i\mid\mathcal E_t\vee\sigma(J_t))=p_t(i)$ a.s., where $p_t$ is the policy evaluated on the learner's observations; $J_t$ and $I_t$ are $\mathcal E_{t+1}$-measurable.
--
--   The learner observes $y_t(I_t)$ only (bandit feedback). This is the protocol of §2.1 with the draw $J_t\sim q_t$ made at the start of the round as in Algorithm 1. The σ-algebra $\mathcal O_{t-1}=\mathcal E_t\vee\sigma(J_t)$ is "all information immediately before sampling $I_t$" (§C.1).
--
--   **Formalization Note** Rounds are $0,\dots,T-1$; conditional probabilities are conditional expectations (`MeasureTheory.condExp`) of indicators; actions carry the discrete σ-algebra. Nothing is assumed about how $q_t$, $y_t$ are generated beyond measurability. A policy receives the drawn $J_t$ and not $q_t$, which Algorithm 1 uses only to draw $J_t$.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §2.1 (Interaction protocol), p.7 (PDF 7); Algorithm 1, p.10; §C.1, p.31 (the σ-algebra $\mathcal O_{t-1}$)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory

/-- A **bandit-feedback learner (policy)** with `K` actions. At round `t` it receives the
recommended actions `J`, the learner's own played actions `I` and the observed rewards `r`
(`r s = y_s(I_s)`, the only feedback of round `s`), and returns the mixed strategy `p_t`. A
concrete policy is expected to read only `J s` for `s ≤ t` and `I s`, `r s` for `s < t`.

**Formalization Note.** The paper's learner "has access to the recommendation `q_t`" (p.7), and
Algorithm 1 (p.10) uses it only to draw `J_t ∼ q_t`; a policy here receives the drawn `J_t` and
not `q_t`. -/
abbrev Policy (K : ℕ) : Type := ℕ → (ℕ → Fin K) → (ℕ → Fin K) → (ℕ → ℝ) → Fin K → ℝ

/-- **A run of the `T`-round interaction protocol** driven by a learner `policy`, on a
probability space `(Ω, P)`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §2.1
"Interaction protocol", p.7: in each round `t ∈ [T]`, (1) the recommendation algorithm gives a
mixed strategy `q_t ∈ Δ(𝒜)` to the learner; (2) the adversary chooses a reward vector
`y_t ∈ [0,1]^K`, not yet revealed to the learner; (3) the learner, who has access to `q_t` and
the feedback from previous rounds, selects `p_t ∈ Δ(𝒜)`, draws `I_t ∼ p_t` and receives
`y_t(I_t)`; `J_t ∼ q_t` is the (hypothetical) action of the recommendation algorithm; (4) the
learner receives `y_t(I_t)` as the feedback. "Both q_t and y_t may depend on the past
interaction, and they may be correlated through information unavailable to the learner. We
impose only a non-anticipation condition. That is, they are chosen before the learner draws any
fresh randomness in round t." Algorithm 1 (p.10) has the learner "Observe q_t and draw a
recommended action J_t ∼ q_t" before choosing its mixed strategy.

Fields:
* `info t` is the σ-algebra of everything fixed before the learner's round-`t` draws: the whole
  past (including the environment's private information), `q_t` and `y_t`. It is a sub-σ-algebra
  of the ambient one and grows from round to round; `J_t` and `I_t` are known at `info (t+1)`.
* `q t ω`, `y t ω` are the recommendation and the reward vector of round `t`; both are
  `info t`-measurable (non-anticipation), `q t ω ∈ Δ(𝒜)` and `y t ω ∈ [0,1]^K`.
* `J t` is drawn from `q t` given `info t`: `P[J_t = j | info t] = q_t(j)` a.s.
* `I t` is drawn from the learner's mixed strategy given `info t` and `J t`:
  `P[I_t = i | info t ∨ σ(J_t)] = p_t(i)` a.s., where `p_t` is `policy` evaluated on the
  learner's observations (`J`, `I`, and the observed rewards `y_s(I_s)`).

**Formalization Note.** Rounds are `t = 0, …, T − 1`; the hypotheses are imposed only on these
rounds (and `info t` for `t ≤ T`). Actions are `Fin K` with the discrete σ-algebra. The draws are
expressed through conditional expectations of indicators (`MeasureTheory.condExp`), so the
environment may be adaptive, randomized and correlated with the recommendation through
information the learner never sees; nothing is assumed about how `q_t` and `y_t` are produced
beyond measurability with respect to `info t`. Bandit feedback is enforced by the policy's
inputs: it sees the rewards only through `y_s(I_s)`. -/
structure ProtocolRun (K T : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (policy : Policy K) where
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
      =ᵐ[P] fun ω => policy t (fun s => J s ω) (fun s => I s ω) (fun s => y s ω (I s ω)) i

namespace ProtocolRun

variable {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {policy : Policy K}

/-- The paper's `𝒪_{t−1}`: "all information immediately before sampling `I_t`" (§C.1, p.31),
i.e. `info t ∨ σ(J_t)`. -/
abbrev preDraw (run : ProtocolRun K T P policy) (t : ℕ) : MeasurableSpace Ω :=
  run.info t ⊔ MeasurableSpace.comap (run.J t) inferInstance

/-- The observed reward `r_t = y_t(I_t)` of round `t`. -/
def obs (run : ProtocolRun K T P policy) (t : ℕ) (ω : Ω) : ℝ :=
  run.y t ω (run.I t ω)

/-- The learner's mixed strategy `p_t` in the run: `policy` applied to the learner's
observations. -/
def played (run : ProtocolRun K T P policy) (t : ℕ) (ω : Ω) : Fin K → ℝ :=
  policy t (fun s => run.J s ω) (fun s => run.I s ω) (fun s => run.obs s ω)

end ProtocolRun

end CalibeatBandit


