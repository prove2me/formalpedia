-- Prove2me | Definitions.Def_OfflineCMC_Minimax_CMC
-- name    : OfflineCMC_Minimax_CMC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:00.424503+00:00
-- url     : https://prove2.me/theorems/4b39ea54-0340-40dc-a60c-2bdec3d72ff4
-- title:
--   Controlled Markov chain: an adapted state–control process with transition matrices M^(l) given the filtration (§2, pp. 6–7)
-- statement:
--   A **controlled Markov chain** (CMC) with $d$ states and $k$ controls is defined on a filtered probability space $(\Omega,\mathcal F,\{\mathcal F_i\}_{i\ge 0},\mathbb P)$. It consists of:
--
--   1. a state process $\{X_i\}_{i\ge 0}$ with values in the finite state space $\chi=\{1,\dots,d\}$;
--   2. a control process $\{a_i\}_{i\ge 0}$ with values in the finite control space $\mathbb I=\{1,\dots,k\}$;
--   3. row-stochastic transition matrices $M^{(1)},\dots,M^{(k)}$, one for each control, with $M^{(l)}_{s,t}\ge 0$ and $\sum_t M^{(l)}_{s,t}=1$.
--
--   Both processes are adapted: $X_i$ and $a_i$ are $\mathcal F_i$-measurable. Given the past, the next state is drawn from the row of the current state under the current control:
--   $$
--   \mathbb P\big(X_{i+1}=t\,\big|\,\mathcal F_i\big)=M^{(a_i)}_{X_i,t}\qquad\text{almost surely, for every } i\ge 0 \text{ and } t\in\chi .
--   $$
--
--   Nothing else is assumed about the controls: they may depend on the whole history and on outside randomness, and need be neither Markov nor time-homogeneous. The initial law of $(X_0,a_0)$ is arbitrary.
--
--   This is the data-generating model of the paper. A deterministic control sequence gives a time-inhomogeneous Markov chain, and a control $a_i=f(X_i)$ gives a Markov chain.
--
--   **Formalization Note** States are `Fin d` and controls `Fin k`. Time is $\mathbb N$ from $0$. The filtration is a Mathlib `Filtration ℕ`. The Markov property is stated with Mathlib's conditional expectation of the indicator of $\{X_{i+1}=t\}$, almost everywhere.
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, pp. 6–7, §2 (Notations, Definitions: controlled Markov chain)

import Mathlib

namespace OfflineCMC.Minimax

open MeasureTheory

/-- A **controlled Markov chain** with `d` states `Fin d` and `k` controls `Fin k` on a measurable
space `Ω` with measure `μ` (Banerjee–Honnappa–Rao, §2, pp. 6–7).

* `𝓕` is a filtration indexed by the times `0, 1, 2, …`;
* the states `X i` and the controls `a i` are adapted to `𝓕` (`a i ∈ 𝓕 i`); nothing else is assumed
  about the controls: they may be non-Markovian and time-inhomogeneous;
* `M l` is the row-stochastic transition matrix of control `l`;
* given `𝓕 i`, the next state has law `M (a i) (X i) ·`:
  `P(X (i+1) = t | 𝓕 i) = M (a i) (X i) t` almost surely, for every time `i` and state `t`.

The initial law of `X 0` (and of `a 0`) is arbitrary. -/
structure CMC (d k : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) where
  /-- The filtration `{𝓕 i}`. -/
  𝓕 : Filtration ℕ mΩ
  /-- The state process. -/
  X : ℕ → Ω → Fin d
  /-- The control process. -/
  a : ℕ → Ω → Fin k
  /-- The transition matrices, `M l s t = M^(l)_{s,t}`. -/
  M : Fin k → Fin d → Fin d → ℝ
  M_nonneg : ∀ l s t, 0 ≤ M l s t
  M_sum : ∀ l s, ∑ t, M l s t = 1
  adaptedX : ∀ i, Measurable[𝓕 i] (X i)
  adapteda : ∀ i, Measurable[𝓕 i] (a i)
  markov : ∀ (i : ℕ) (t : Fin d),
    μ[{ω | X (i + 1) ω = t}.indicator (fun _ => (1 : ℝ)) | 𝓕 i]
      =ᵐ[μ] fun ω => M (a i ω) (X i ω) t

end OfflineCMC.Minimax


