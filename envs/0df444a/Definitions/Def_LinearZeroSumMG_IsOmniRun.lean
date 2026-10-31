-- Prove2me | Definitions.Def_LinearZeroSumMG_IsOmniRun
-- name    : LinearZeroSumMG_IsOmniRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:53:56.927247+00:00
-- url     : https://prove2.me/theorems/dd7d3c94-e595-41a1-91d4-d6c6925a91e9
-- title:
--   A run of Algorithm 1 for $K$ episodes
-- statement:
--   On a probability space with a filtration $(\mathcal F_n)$, a **run of Algorithm 1** consists of random states $x^k_h$ ($k\in[K]$, $h\in[H+1]$) and random actions $a^k_h$ (P1), $b^k_h$ (P2) ($h\in[H]$) such that, with $s(k,h)=2((k-1)(H+1)+(h-1))$:
--   1. $x^k_h$ is $\mathcal F_{s(k,h)}$-measurable; nothing else is required of the initial state $x^k_1$, which may be chosen from everything observed before episode $k$;
--   2. $(a^k_h,b^k_h)$ is $\mathcal F_{s(k,h)+1}$-measurable;
--   3. given $\mathcal F_{s(k,h)}$, the pair $(a^k_h,b^k_h)$ has law $\sigma^k_h(x^k_h)$, computed by Algorithm 1 from the data of episodes $\tau<k$;
--   4. given $\mathcal F_{s(k,h)+1}$, the next state $x^k_{h+1}$ has law $\mathbb P_h(\cdot\mid x^k_h,a^k_h,b^k_h)$.
--
--   This models lines 14–18 of Algorithm 1 and the episodic protocol of §3.1: at the start of each episode an initial state is chosen, then the players act and the game moves.
--
--   **Formalization Note** The conditional laws are almost-sure identities of conditional expectations of indicators. The paper's filtration (10) is coarser than any filtration satisfying 1–2.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §3.1, p.9; Algorithm 1, lines 14–18, p.10; (10), p.17

import Mathlib
import Definitions.Def_LinearZeroSumMG_omni

namespace LinearZeroSumMG

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] {d : ℕ}

/-- The filtration index at which the state `x^k_h` is observed, for `k ≥ 1` and
`h ∈ {1, …, H + 1}`: `s(k, h) = 2((k − 1)(H + 1) + (h − 1))`. The actions `(a^k_h, b^k_h)` are played
at index `s(k, h) + 1`. -/
def sIdx (H k h : ℕ) : ℕ := 2 * ((k - 1) * (H + 1) + (h - 1))

/-- **A run of Algorithm 1 for `K` episodes.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §3.1, p.9 ("In the episodic setting,
the Markov game is played for `K` episodes, each of which consists of `H` timesteps. At the beginning
of the `k`-th episode, an arbitrary initial state `x^k_1` is chosen.") and Algorithm 1, lines 14–18,
p.10 ("Sample `(a^k_h, b^k_h) ∼ σ^k_h(x^k_h)`. P1 takes action `a^k_h`; P2 takes action `b^k_h`.
Observe next state `x^k_{h+1}`.").

On a measure space `(Ω, μ)` with filtration `𝓕`, the random states are `x k h = x^k_h` and the
random actions `a k h = a^k_h` (P1), `b k h = b^k_h` (P2). `IsOmniRun μ 𝓕 G P K x a b` says, for
`k ∈ [1, K]`:
1. `x^k_h` is `𝓕_{s(k,h)}`-measurable for `h ∈ [1, H + 1]`; nothing else is required of the initial
   state `x^k_1`, which may be chosen from everything observed before;
2. `(a^k_h, b^k_h)` is `𝓕_{s(k,h)+1}`-measurable for `h ∈ [1, H]`;
3. given `𝓕_{s(k,h)}`, the action pair `(a^k_h, b^k_h)` has law `σ^k_h(x^k_h)`, where `σ^k_h` is computed
   by Algorithm 1 from the data of the episodes `τ < k` of the same path;
4. given `𝓕_{s(k,h)+1}`, the next state `x^k_{h+1}` has law `ℙ_h(· | x^k_h, a^k_h, b^k_h)`.

**Formalization Note** The conditional laws are stated as almost-everywhere identities of
conditional expectations of indicators. Filtration (10) of the paper (p.17) is coarser than any `𝓕`
satisfying 1–2; an adaptively chosen initial state generalizes "an arbitrary initial state". -/
structure IsOmniRun {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (G : MarkovGame S A) (P : OmniParams S A d) (K : ℕ)
    (x : ℕ → ℕ → Ω → S) (a b : ℕ → ℕ → Ω → A) : Prop where
  state_adapted : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 (G.H + 1),
    Measurable[𝓕 (sIdx G.H k h)] (x k h)
  action_adapted : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 G.H,
    Measurable[𝓕 (sIdx G.H k h + 1)] (fun ω => (a k h ω, b k h ω))
  action_law : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 G.H, ∀ a₀ b₀ : A,
    μ[{ω | a k h ω = a₀ ∧ b k h ω = b₀}.indicator (fun _ => (1 : ℝ)) | 𝓕 (sIdx G.H k h)]
      =ᵐ[μ] fun ω =>
        (omni G P (fun τ i => x τ i ω) (fun τ i => a τ i ω) (fun τ i => b τ i ω) k h).sigma
          (x k h ω) (a₀, b₀)
  transition : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 G.H, ∀ B : Set S, MeasurableSet B →
    μ[(x k (h + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) | 𝓕 (sIdx G.H k h + 1)]
      =ᵐ[μ] fun ω => (G.P h (x k h ω, a k h ω, b k h ω) B).toReal

end LinearZeroSumMG


