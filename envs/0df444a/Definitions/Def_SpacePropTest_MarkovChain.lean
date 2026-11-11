-- Prove2me | Definitions.Def_SpacePropTest_MarkovChain
-- name    : SpacePropTest_MarkovChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:53.509257+00:00
-- url     : https://prove2.me/theorems/8b21fe03-8153-4b69-8c3c-649431102ae9
-- title:
--   Finite Markov chains and the long-run state probability $\hat p_C(s)$
-- statement:
--   A **Markov chain** on a finite state set $\sigma$ is a stochastic matrix $C$: $C(s,s')\ge0$ and $\sum_{s'}C(s,s')=1$. Started at $s_0$, it is in state $s$ at time $t$ with probability $(C^t)(s_0,s)$. The **long-run probability** of $s$ is the limit of the Cesàro averages
--
--   $$\hat p_C(s)=\lim_{T\to\infty}\frac1T\sum_{t=0}^{T-1}\Pr[C\text{ is in state }s\text{ at time }t].$$
--
--   Testers in this paper decide by long-run probabilities, so these are the quantities every upper and lower bound controls.
--
--   **Formalization Note** The limit is taken with `limUnder`; it exists for every finite chain (Theorem 62 states the convergence with `Tendsto`). The $T=0$ term of the averaged sequence is $0$ and does not affect the limit.
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), §4.1, pp.15–16 (PDF 17–18); App. A.1, Theorem 62, p.53 (PDF 55)

import Mathlib

set_option autoImplicit false

namespace SpacePropTest

noncomputable section

open Filter

/-- **Finite Markov chains and long-run state probabilities** (C. Canonne, X. Chen, W. Pires,
T. Pitassi, R. A. Servedio, *The Space Complexity of Property Testing*, manuscript of November 2,
2026, sha256 65850aa6…; §4.1, pp.15–16 (PDF 17–18); App. A.1, Theorem 62, p.53 (PDF 55)).

A Markov chain on a finite state type `σ` is a stochastic matrix `C` (nonnegative entries, rows
summing to 1). -/
def IsStochastic {σ : Type*} [Fintype σ] (C : Matrix σ σ ℝ) : Prop :=
  (∀ s s', 0 ≤ C s s') ∧ ∀ s, ∑ s', C s s' = 1

/-- `Pr[C is in state s at time t]` for the chain started at `s₀`: the entry `(Cᵗ)(s₀, s)`. -/
def occ {σ : Type*} [Fintype σ] [DecidableEq σ] (C : Matrix σ σ ℝ) (s₀ s : σ) (t : ℕ) : ℝ :=
  (C ^ t) s₀ s

/-- The Cesàro average `(1/T) ∑_{t=0}^{T-1} Pr[C is in state s at time t]`. -/
def cesaro {σ : Type*} [Fintype σ] [DecidableEq σ] (C : Matrix σ σ ℝ) (s₀ s : σ) (T : ℕ) : ℝ :=
  (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, occ C s₀ s t

/-- The long-run probability `p̂_C(s) = lim_{T→∞} (1/T) ∑_{t<T} Pr[C in state s at time t]`.

**Formalization Note.** Written with `limUnder`; the limit exists for every finite chain, which
is part of Theorem 62 (stated there with `Tendsto`). The `T = 0` term of the sequence is `0` and
does not affect the limit. -/
def longRun {σ : Type*} [Fintype σ] [DecidableEq σ] (C : Matrix σ σ ℝ) (s₀ s : σ) : ℝ :=
  limUnder atTop (cesaro C s₀ s)

end

end SpacePropTest


