-- Prove2me | Definitions.Def_KellyKolmogorov_HasRegularPaths
-- name    : KellyKolmogorov_HasRegularPaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:47.963562+00:00
-- url     : https://prove2.me/theorems/8fc718a3-650e-4a1a-8e99-7e3795cd0990
-- title:
--   Regular sample paths (positive holding times, no explosion)
-- statement:
--   A process $X(t)$, $t\in\mathbb R$, with values in a countable set $\mathcal S$ has **regular sample paths** if for almost every outcome $\omega$ the path $t\mapsto X(t,\omega)$
--
--   1. is right-continuous: for every $t$ there is $\varepsilon>0$ with $X(s,\omega)=X(t,\omega)$ for all $s\in[t,t+\varepsilon)$;
--   2. has finitely many jump points in every bounded interval $[a,b]$, where $t$ is a jump point if every neighbourhood of $t$ contains a time $s$ with $X(s,\omega)\ne X(t,\omega)$.
--
--   These are the book's standing conditions that the process "remains in each state for a positive length of time and is incapable of passing through an infinite number of states in a finite time", with the usual convention that the process is right continuous at its jumps (Exercise 1.2.1).
--
--   **Formalization Note** The finite-dimensional distributions cannot distinguish the right-continuous convention from another convention at jump times (Exercise 1.2.1, p. 9).
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.1, pp. 2–3 (PDF pp. 5–6), standing assumptions; Exercise 1.2.1, p. 9 (PDF p. 12), right-continuity convention

import Mathlib

open MeasureTheory

namespace KellyKolmogorov

/-- **Regular sample paths: positive holding times and no explosion.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.1, pp. 2–3: "throughout this work
we shall assume that any continuous time Markov process with which we deal is not only time
homogeneous and irreducible but also remains in each state for a positive length of time and is
incapable of passing through an infinite number of states in a finite time." Exercise 1.2.1,
p. 9: "The usual convention is that if `X(t)` jumps at time `t₀` then `X(t₀)` is taken to be the
new state, so that the process is right continuous."

For almost every `ω`, the sample path `t ↦ X t ω`
1. is right-continuous: at every `t` it stays at `X t ω` on some interval `[t, t + ε)`, `ε > 0`;
2. has finitely many jump points in every bounded interval `[a, b]`, a jump point being a time
   `t` such that every neighbourhood of `t` contains a time `s` with `X s ω ≠ X t ω`.

**Formalization Note.** Together the two clauses say that the path is piecewise constant with
finitely many jumps on bounded intervals: it stays in each state for a positive length of time
and visits finitely many states in finite time. The finite-dimensional distributions cannot
distinguish this from another convention at jump times (Exercise 1.2.1). -/
def HasRegularPaths {Ω 𝒮 : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ → Ω → 𝒮) : Prop :=
  ∀ᵐ ω ∂μ, (∀ t : ℝ, ∃ ε > 0, ∀ s ∈ Set.Ico t (t + ε), X s ω = X t ω) ∧
    ∀ a b : ℝ,
      {t ∈ Set.Icc a b | ∀ ε > 0, ∃ s ∈ Set.Ioo (t - ε) (t + ε), X s ω ≠ X t ω}.Finite

end KellyKolmogorov


