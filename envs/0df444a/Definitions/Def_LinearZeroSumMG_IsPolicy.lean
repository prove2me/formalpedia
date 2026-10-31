-- Prove2me | Definitions.Def_LinearZeroSumMG_IsPolicy
-- name    : LinearZeroSumMG_IsPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:13.799003+00:00
-- url     : https://prove2.me/theorems/7421d135-b707-434e-8b07-4c04ccc0e377
-- title:
--   Stochastic Markov policy $\pi=(\pi_h:\mathcal S\to\Delta(\mathcal A))_{h\in[H]}$
-- statement:
--   A **stochastic policy** of a player is a sequence $\pi=(\pi_h)_{h\in[H]}$ of maps $\pi_h:\mathcal S\to\Delta(\mathcal A)$, where $\Delta(\mathcal A)$ is the probability simplex over the action set: at step $h$ in state $x$ the player samples an action from $\pi_h(x)$. The maps are required to be measurable in the state.
--
--   Policies of both players have this form; the value functions, the best responses and the duality gap are defined over them.
--
--   **Formalization Note** A policy is a function $\pi:\mathbb N\to\mathcal S\to\mathcal A\to\mathbb R$ with $\pi_h(x)$ in Mathlib's `stdSimplex ℝ A` for every $h$ and $x$; measurability in the state is with respect to the product σ-algebra on $\mathbb R^{\mathcal A}$.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §2.2, p.6

import Mathlib

namespace LinearZeroSumMG

/-- **Stochastic (Markov) policy.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §2.2, p.6: "Denote by
`Δ ≡ Δ(𝒜)` the probability simplex over the action space `𝒜`. A stochastic policy of P1 is a
length-`H` sequence of functions `π := (π_h : 𝒮 → Δ)_{h∈[H]}`. At each step `h ∈ [H]` and state
`x ∈ 𝒮`, P1 takes an action sampled from the distribution `π_h(x)` over `𝒜`. Similarly, a stochastic
policy of P2 is given by the sequence `ν := (ν_h : 𝒮 → Δ)_{h∈[H]}`."

`IsPolicy π` says that `π h x ∈ Δ(A)` for every step `h` and state `x`, and that `x ↦ π h x` is
measurable.

**Formalization Note** A policy is a function `π : ℕ → S → A → ℝ`, `π h x a` being the probability
of action `a` at step `h` in state `x`; only the steps `h ∈ [1, H]` are ever read. The simplex is
Mathlib's `stdSimplex ℝ A`. Measurability in the state (for the product σ-algebra on `A → ℝ`) is
required so that expected values under the transition kernel are defined; it excludes only policies
whose values the paper could not define. -/
def IsPolicy {S A : Type*} [MeasurableSpace S] [Fintype A] (π : ℕ → S → A → ℝ) : Prop :=
  ∀ h, Measurable (π h) ∧ ∀ x, π h x ∈ stdSimplex ℝ A

end LinearZeroSumMG


