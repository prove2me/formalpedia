-- Prove2me | Definitions.Def_StochCoordProx_Assumption2
-- name    : StochCoordProx_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:33.767422+00:00
-- url     : https://prove2.me/theorems/8f91858c-62cb-4c9d-bf80-7fad2e013fbc
-- title:
--   Assumption 2 (well-alignment with probability $\ge 1-\delta$)
-- statement:
--   Let $(\Omega,P)$ be a probability space with a filtration $(\mathcal F_k)_{k\ge0}$, let $W_k\subseteq\Omega$ be the event "$U_k$ is well-aligned", and let $\delta\in\mathbb R$. **Assumption 2** holds if at each iteration the event has conditional probability at least $1-\delta$ given the past:
--
--   1. $W_k$ is $\mathcal F_{k+1}$-measurable for every $k$;
--   2. $P[W_k\mid\mathcal F_k]\ge1-\delta$ almost surely, for every $k$.
--
--   The paper states: "At each iteration $k$ our subspace selection $U_k$ is well-aligned for some fixed $\alpha\in(0,1)$ with probability at least $1-\delta$, with $\delta\in(0,1)$, independently of the filtration $\mathcal F_k:=\{U_0,\dots,U_{k-1}\}$." Scaled sampling matrices and Johnson–Lindenstrauss embeddings satisfy it (§3.1–3.2).
--
--   **Formalization Note** The statement is read as a conditional probability given $\mathcal F_k$, written `P⟦W k | 𝓕 k⟧`, the conditional expectation of the indicator. Alignment of $U_k$ is measured at $x_k$, which depends on the past, so a per-step bound must be conditional. The filtration is any filtration to which the events are adapted; the paper's $\sigma(U_0,\dots,U_{k-1})$ is one instance.
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Assumption 2, p.8

import Mathlib

open MeasureTheory
open scoped ProbabilityTheory

namespace StochCoordProx

/-- **Assumption 2** (subspace quality): at each iteration `k` the event
`W k = {U_k is well-aligned}` has probability at least `1 − δ` given the past `𝓕_k`:
1. `W k` is `𝓕_{k+1}`-measurable (it is determined by `U₀, …, U_k`), and
2. `P[W k | 𝓕_k] ≥ 1 − δ` almost surely.

Necoara & Chorobura, arXiv:2104.13370v3, Assumption 2, p.8.

**Formalization Note.** The paper's "with probability at least `1 − δ` … independently of the
filtration `𝓕_k := {U₀, …, U_{k−1}}`" is read as a conditional probability given `𝓕_k`:
`P⟦W k | 𝓕 k⟧ = P[1_{W k} | 𝓕 k]` (Mathlib's conditional expectation of the indicator).
The filtration is any filtration `𝓕 : Filtration ℕ m0` to which the events are adapted
(`W k ∈ 𝓕 (k+1)`); the paper's `σ(U₀, …, U_{k−1})` is one instance. The bound `δ ∈ (0,1)` is a
hypothesis of the statements that use the predicate. -/
def Assumption2 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℕ m0)
    (W : ℕ → Set Ω) (δ : ℝ) : Prop :=
  (∀ k : ℕ, MeasurableSet[𝓕 (k + 1)] (W k)) ∧
    ∀ k : ℕ, ∀ᵐ ω ∂P, 1 - δ ≤ (P⟦W k | 𝓕 k⟧) ω

end StochCoordProx


