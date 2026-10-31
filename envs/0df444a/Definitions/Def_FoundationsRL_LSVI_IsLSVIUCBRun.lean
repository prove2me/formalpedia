-- Prove2me | Definitions.Def_FoundationsRL_LSVI_IsLSVIUCBRun
-- name    : FoundationsRL_LSVI_IsLSVIUCBRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:23:58.697983+00:00
-- url     : https://prove2.me/theorems/d4b5f893-e82e-47af-89c3-a7fade5c60ab
-- title:
--   A run of LSVI-UCB in an MDP on a filtered probability space
-- statement:
--   A **run of LSVI-UCB** with inputs $R,\rho$ for $T$ episodes of horizon $H$ in an MDP $M$ consists of a probability space $(\Omega,\mu)$ with a filtration $(\mathcal F_n)$, random states $s^t_h$, rewards $r^t_h$, least-squares solutions $\hat\theta^t_h$ and greedy policies $\hat\pi^t$, such that for every episode $t\in[T]$ and step $h\in[H]$:
--
--   1. $\hat\theta^t_h$ and $\hat\pi^t$ are determined before episode $t$ starts: $\hat\theta^t_h$, and the feature and transition and reward laws of every action $\hat\pi^t_h(s)$, are measurable with respect to the information at the start of episode $t$;
--   2. $s^t_h$ is observed at step $h$ and $r^t_h$ right after it;
--   3. $s^t_1\sim d_1$ independently of the past; given the past up to $s^t_h$, $s^t_{h+1}\sim P^M_h(\cdot\mid s^t_h,a^t_h)$ for $h<H$ and $r^t_h\sim R^M_h(s^t_h,a^t_h)$, where $a^t_h=\hat\pi^t_h(s^t_h)$;
--   4. along every realization, LSVI-UCB's computations hold (`IsLSVITrace`).
--
--   This is the probabilistic setting in which Lemma 27 and Proposition 46 are statements.
--
--   **Formalization Note** The information is indexed by slots $(t,h)$, $h=0,\dots,H$, flattened to $(t-1)(H+1)+h$; slot $(t,0)$ is the start of episode $t$. Adaptedness is expressed without a $\sigma$-algebra on $\mathcal S$ or $\mathcal A$: through the events $\{s^t_h=s\}$ and through the quantities by which an action enters the interaction. The joint law of $r^t_h$ and $s^t_{h+1}$ given the past is left free.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, algorithm box LSVI-UCB, p. 133; episode protocol of §5.1, p. 81

import Mathlib
import Definitions.Def_FoundationsRL_LSVI_EpisodicMDP
import Definitions.Def_FoundationsRL_LSVI_IsLSVITrace

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LSVI

/-- The time index of the interaction: slot `(t, 0)` is the start of episode `t` (everything
observed in episodes `1, …, t − 1`), and slot `(t, h)`, `h ∈ [H]`, is the moment the state
`s^t_h` has been observed (together with `r^t_1, …, r^t_{h−1}`):
`timeIdx H t h = (t − 1)(H + 1) + h`. -/
def timeIdx (H t h : ℕ) : ℕ := (t - 1) * (H + 1) + h

/-- A run of LSVI-UCB with inputs `R, ρ` for `T` episodes of horizon `H` in the MDP `M`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, algorithm box, p. 133, and the episode protocol of §5.1, p. 81), on a
probability space `(Ω, μ)` with filtration `𝓕`. The random objects are the states
`st t h = s^t_h`, the rewards `rw t h = r^t_h`, the least-squares solutions `θhat t h = θ̂^t_h`
and the greedy policies `pol t h x = π̂^t_h(x)`; the action is `a^t_h = π̂^t_h(s^t_h)`.
For every episode `t ∈ [T]`:

1. `θ̂^t_h` and `π̂^t_h(x)` are computed before episode `t` starts (`𝓕_{(t,0)}`-measurable);
2. `s^t_h` is observed at slot `(t, h)`, and `r^t_h` by slot `(t, h)` plus one;
3. `s^t_1 ∼ d₁` given the past; given everything up to slot `(t, h)`,
   `s^t_{h+1} ∼ P^M_h(· | s^t_h, a^t_h)` (for `h < H`) and `r^t_h ∼ R^M_h(s^t_h, a^t_h)`;
4. along every realization the algorithm's computations hold (`IsLSVITrace`).

**Formalization Note.** Adaptedness is stated without a σ-algebra on `S` or `A`: through the
events `{s^t_h = x}` (`S` is countable) and, for the policy, through the feature `ϕ(x, π̂^t_h(x))`
and the laws `P^M_h(· | x, π̂^t_h(x))`, `R^M_h(x, π̂^t_h(x))`, the only ways an action enters the
interaction and the algorithm. The conditional laws are stated through conditional expectations of
indicators. The joint law of `r^t_h` and `s^t_{h+1}` given the past is left free (the book draws
them from `R^M_h` and `P^M_h`); every coupling is allowed. The terminal state `s^t_{H+1}` plays no
role, since `Q̄^t_{H+1} ≡ 0`. -/
structure IsLSVIUCBRun {S A : Type*} {d : ℕ}
    (M : EpisodicMDP S A) (ϕ : S → A → EuclideanSpace ℝ (Fin d)) (R ρ : ℝ) (H T : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
    (st : ℕ → ℕ → Ω → S) (rw : ℕ → ℕ → Ω → ℝ)
    (θhat : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (pol : ℕ → ℕ → S → Ω → A) : Prop where
  /-- `θ̂^t_h` is computed from the episodes before `t`. -/
  theta_meas : ∀ t ∈ Finset.Icc 1 T, ∀ h ∈ Finset.Icc 1 H,
    Measurable[𝓕 (timeIdx H t 0)] (θhat t h)
  /-- `π̂^t` is computed from the episodes before `t`: at every `(h, x)`, the feature, the
  transition law and the reward law of the action `π̂^t_h(x)` are known at the start of
  episode `t`. -/
  pol_meas : ∀ t ∈ Finset.Icc 1 T, ∀ h ∈ Finset.Icc 1 H, ∀ x,
    Measurable[𝓕 (timeIdx H t 0)] (fun ω => ϕ x (pol t h x ω)) ∧
    (∀ y, Measurable[𝓕 (timeIdx H t 0)] (fun ω => (M.P h x (pol t h x ω) y).toReal)) ∧
    (∀ B : Set ℝ, MeasurableSet B →
      Measurable[𝓕 (timeIdx H t 0)] (fun ω => (M.R h x (pol t h x ω) B).toReal))
  /-- `s^t_h` is observed at slot `(t, h)`. -/
  state_meas : ∀ t ∈ Finset.Icc 1 T, ∀ h ∈ Finset.Icc 1 H, ∀ x : S,
    MeasurableSet[𝓕 (timeIdx H t h)] {ω | st t h ω = x}
  /-- `r^t_h` is observed by the next slot. -/
  reward_meas : ∀ t ∈ Finset.Icc 1 T, ∀ h ∈ Finset.Icc 1 H,
    Measurable[𝓕 (timeIdx H t h + 1)] (rw t h)
  /-- `s^t_1 ∼ d₁`, independently of the past. -/
  init_law : ∀ t ∈ Finset.Icc 1 T, ∀ x : S,
    μ[Set.indicator {ω | st t 1 ω = x} (fun _ => (1 : ℝ)) | 𝓕 (timeIdx H t 0)]
      =ᵐ[μ] fun _ => (M.d1 x).toReal
  /-- `s^t_{h+1} ∼ P^M_h(· | s^t_h, a^t_h)` given the past. -/
  trans_law : ∀ t ∈ Finset.Icc 1 T, ∀ h ∈ Finset.Ico 1 H, ∀ x : S,
    μ[Set.indicator {ω | st t (h + 1) ω = x} (fun _ => (1 : ℝ)) | 𝓕 (timeIdx H t h)]
      =ᵐ[μ] fun ω => (M.P h (st t h ω) (pol t h (st t h ω) ω) x).toReal
  /-- `r^t_h ∼ R^M_h(s^t_h, a^t_h)` given the past. -/
  reward_law : ∀ t ∈ Finset.Icc 1 T, ∀ h ∈ Finset.Icc 1 H, ∀ B : Set ℝ, MeasurableSet B →
    μ[Set.indicator {ω | rw t h ω ∈ B} (fun _ => (1 : ℝ)) | 𝓕 (timeIdx H t h)]
      =ᵐ[μ] fun ω => (M.R h (st t h ω) (pol t h (st t h ω) ω) B).toReal
  /-- Along every realization, LSVI-UCB's computations hold. -/
  trace : ∀ ω, IsLSVITrace ϕ R ρ H T (fun t h => st t h ω) (fun t h => rw t h ω)
    (fun t h => θhat t h ω) (fun t h x => pol t h x ω)

end FoundationsRL.LSVI


