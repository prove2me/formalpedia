-- Prove2me | Definitions.Def_PoissonDirichlet_Chain_Markov
-- name    : PoissonDirichlet_Chain_Markov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:30.54263+00:00
-- url     : https://prove2.me/theorems/d6447cc6-5980-4ef8-bbb5-a5da4b4ac87a
-- title:
--   Markov chain on ℝ with given forward transition kernels
-- statement:
--   Let $(Y_1, Y_2, \dots)$ be a sequence of real random variables on a probability space $(\Omega, P)$, and let $\kappa_1, \kappa_2, \dots$ be kernels from $\mathbb R$ to $\mathbb R$. We say that **under $P$, $(Y_n)$ is a Markov chain with forward transition kernels $(\kappa_n)$** if, for every $n \ge 1$, the conditional law of $Y_{n+1}$ given $Y_1, \dots, Y_n$ is $\kappa_n(Y_n, \cdot)$. Equivalently, for all nonnegative measurable $g$ on $\mathbb R^n$ and $h$ on $\mathbb R$,
--   $$E\big[g(Y_1,\dots,Y_n)\,h(Y_{n+1})\big] = E\Big[g(Y_1,\dots,Y_n)\int h(y)\,\kappa_n(Y_n, dy)\Big].$$
--
--   This is the notion in which Theorem 38 (ii) of Pitman and Yor asserts that two different laws govern $(Y_n)$ "as a Markov chain with the same forward transition probabilities".
--
--   **Formalization Note.** Indices are 0-based: `Y ω k` is $Y_{k+1}$ and `κ k` is the transition from step $k+1$ to $k+2$. Whether the kernels are Markov (probability) kernels is stated separately where it is needed.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 886, Proposition 37; p. 887, Theorem 38 (ii)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace PoissonDirichlet.Chain

/-- `IsMarkovWith P Y κ`: under `P`, the real-valued sequence `Y = (Y 0, Y 1, …)` is a Markov
chain whose forward transition from step `k` to step `k+1` is the kernel `κ k`: for every `k`,
the conditional law of `Y (k+1)` given `(Y 0, …, Y k)` is `κ k (Y k)`. It is stated through the
defining identity of the conditional law: for all nonnegative measurable `g` of the past and
`h` of the next state,
`E[g(Y_0, …, Y_k) h(Y_{k+1})] = E[g(Y_0, …, Y_k) ∫ h dκ_k(Y_k)]`. -/
def IsMarkovWith {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℕ → ℝ)
    (κ : ℕ → Kernel ℝ ℝ) : Prop :=
  ∀ k : ℕ, ∀ g : (Fin (k + 1) → ℝ) → ENNReal, Measurable g →
    ∀ h : ℝ → ENNReal, Measurable h →
      ∫⁻ ω, g (fun i => Y ω i) * h (Y ω (k + 1)) ∂P =
        ∫⁻ ω, g (fun i => Y ω i) * (∫⁻ y, h y ∂(κ k (Y ω k))) ∂P

end PoissonDirichlet.Chain


