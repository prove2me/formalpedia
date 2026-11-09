-- Prove2me | Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain
-- name    : HypergraphUnreliability_FPRAS_JumpChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:50.76028+00:00
-- url     : https://prove2.me/theorems/dc011f8c-61df-4a49-8ea3-14a55c0daff5
-- title:
--   Finite-state continuous-time Markov chains: path law, terminal law and total variation
-- statement:
--   Let $S$ be a finite state space and $q$ a rate function. A **path** to time $T$ records the number $j$ of jumps, the visited states $x_0,\dots,x_j$ and the jump times $0<t_1<\dots<t_j<T$. With $t_0=0$, $t_{j+1}=T$, $\Delta_i=t_{i+1}-t_i$ and exit rates $q(x)=\sum_{y\ne x}q(x,y)$, its density is
--   $$\prod_{i<j}q(x_i,x_{i+1})\ \exp\Bigl(-\sum_{i=0}^{j}q(x_i)\Delta_i\Bigr),$$
--   the last holding interval included. The **expectation** of a path functional $F$ under the chain started at $x_0$ is the sum over $j$ and $(x_1,\dots,x_j)$ of the integral of density times $F$ over the ordered jump times. The **terminal law** at $T$ is the expectation of the indicators of the final state. Along a path, $\int_0^T f(X_t)\,dt=\sum_i f(x_i)\Delta_i$.
--
--   The **total variation distance** of two laws on a finite set is $\frac12\sum_x|a(x)-b(x)|$.
--
--   This is the general object used for the original process, the safe process and the absorbing process.
--
--   **Formalization Note** For bounded rates and a bounded functional measurable in the jump times, each integrand is bounded on a bounded domain and the series is absolutely summable, so neither the junk value of the Bochner integral nor that of `tsum` is met. At $j=0$ the integral is over the one-point space `Fin 0 → ℝ`. A published finite-chain definition (`LambdaCoalescent.Rates.IsRateChain`) fixes only finite-dimensional laws and has no path functionals, so it cannot express Lemma 5.1.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), §3, p. 5; proof of Lemma 5.1, p. 6

import Mathlib

noncomputable section

open scoped BigOperators Classical
open MeasureTheory

namespace HypergraphUnreliability.FPRAS

/-- A finite-state piecewise-constant path: `jumps` jumps, the states visited
`states 0, …, states jumps`, and the jump times `times`. -/
structure JumpPath (S : Type) where
  jumps : ℕ
  states : Fin (jumps + 1) → S
  times : Fin jumps → ℝ

namespace JumpPath

variable {S : Type}

/-- The state at the observation time. -/
def last (π : JumpPath S) : S := π.states (Fin.last _)

/-- The grid `t₀ = 0 < t₁ < ⋯ < t_j < t_{j+1} = T`. -/
def grid (π : JumpPath S) (T : ℝ) : Fin (π.jumps + 2) → ℝ :=
  Fin.cons 0 (Fin.snoc (α := fun _ => ℝ) π.times T)

/-- The holding interval `Δ_i = t_{i+1} - t_i` of the `i`-th visited state, including the final
interval up to the observation time `T`. -/
def holding (π : JumpPath S) (T : ℝ) (i : Fin (π.jumps + 1)) : ℝ :=
  π.grid T i.succ - π.grid T i.castSucc

/-- `∫_0^T f(X_t) dt` along a path. -/
def pathIntegral (f : S → ℝ) (T : ℝ) (π : JumpPath S) : ℝ :=
  ∑ i, f (π.states i) * π.holding T i

end JumpPath

section Chain

variable {S : Type} [Fintype S]

/-- The off-diagonal jump rate; a self-transition is no jump. -/
def jumpRate (q : S → S → ℝ) (x y : S) : ℝ :=
  if x = y then 0 else q x y

/-- The holding rate of `x`. -/
def exitRate (q : S → S → ℝ) (x : S) : ℝ :=
  ∑ y, jumpRate q x y

/-- The density, on a fixed sequence of visited states and with respect to Lebesgue measure on the
jump times, of the finite-state continuous-time Markov chain with rates `q`, observed to time `T`:
the product of the jump rates times the exponential of minus the holding integral, the last holding
interval included. -/
def pathDensity (q : S → S → ℝ) (T : ℝ) (π : JumpPath S) : ℝ :=
  (∏ i : Fin π.jumps, jumpRate q (π.states i.castSucc) (π.states i.succ)) *
    Real.exp (-JumpPath.pathIntegral (exitRate q) T π)

/-- The ordered jump times `0 < t₁ < ⋯ < t_j < T`. -/
def orderedTimes (j : ℕ) (T : ℝ) : Set (Fin j → ℝ) :=
  {t | StrictMono t ∧ ∀ i, 0 < t i ∧ t i < T}

/-- The expectation `E[F]` of a path functional under the law, started at `x₀` and observed to time
`T`, of the continuous-time Markov chain with rates `q`: the sum over the number of jumps and the
visited states of the integral of density times functional over the ordered jump times.
For a bounded functional measurable in the jump times and bounded rates the integrals converge and
the series is absolutely summable, so neither junk value of `∫` or `∑'` is met. -/
def chainExpect (q : S → S → ℝ) (x₀ : S) (T : ℝ) (F : JumpPath S → ℝ) : ℝ :=
  ∑' j : ℕ, ∑ s : Fin (j + 1) → S,
    if s 0 = x₀ then
      ∫ t in orderedTimes j T, pathDensity q T ⟨j, s, t⟩ * F ⟨j, s, t⟩
    else 0

/-- The law of the state at time `T`. -/
def chainLaw (q : S → S → ℝ) (x₀ : S) (T : ℝ) (y : S) : ℝ :=
  chainExpect q x₀ T (fun π => if π.last = y then 1 else 0)

/-- `π` is a path of the chain: it starts at `x₀`, its jump times are ordered in `(0, T)`, and each
of its jumps has positive rate. -/
def IsChainPath (q : S → S → ℝ) (x₀ : S) (T : ℝ) (π : JumpPath S) : Prop :=
  π.states 0 = x₀ ∧ π.times ∈ orderedTimes π.jumps T ∧
    ∀ i : Fin π.jumps, 0 < jumpRate q (π.states i.castSucc) (π.states i.succ)

/-- A bounded measurable path functional: uniformly bounded, and measurable in the jump times on
each sequence of visited states (the paths form a countable union of those pieces). -/
def IsBoundedMeasurableFunctional (F : JumpPath S → ℝ) : Prop :=
  (∃ C : ℝ, ∀ π, |F π| ≤ C) ∧
    ∀ (j : ℕ) (s : Fin (j + 1) → S), Measurable (fun t : Fin j → ℝ => F ⟨j, s, t⟩)

/-- Total variation distance between two finite laws. -/
def tvDist {α : Type} [Fintype α] (a b : α → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |a x - b x|

end Chain

end HypergraphUnreliability.FPRAS


