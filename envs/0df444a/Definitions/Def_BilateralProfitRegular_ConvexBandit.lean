-- Prove2me | Definitions.Def_BilateralProfitRegular_ConvexBandit
-- name    : BilateralProfitRegular_ConvexBandit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:18:24.088801+00:00
-- url     : https://prove2.me/theorems/2546f96e-75cf-440c-b478-9210621b208b
-- title:
--   Stochastic zeroth-order bandits: adaptive algorithms, observation kernels and the expected regret
-- statement:
--   An **algorithm** with query space $X$ draws a seed $\omega$ from $(\Omega,P)$. Its $\tau$-th query $x_\tau$ is a jointly measurable function of $\omega$ and of the past (query, observation) pairs. An **observation environment** is a sequence of Markov kernels: given the past pairs and the current query $x$, it gives the conditional law of the observation.
--
--   **MeanOn** $L,\mathcal K$ says that at every query $x\in\mathcal K$ the observation is integrable with conditional mean $L(x)$, for every history. **ValuesIn** says that the observation lies in a given set almost surely.
--
--   Three expectations are defined:
--
--   1. the expected regret $\mathbb E\big[\sum_{\tau<n}(L(x_\tau)-\min_{\mathcal K}L)\big]$ of $n$ queries;
--   2. the expectation $\mathbb E[f(\text{trajectory})]$ of a nonnegative function of the length-$n$ trajectory;
--   3. the same expectation over $M$ independent runs.
--
--   **Formalization Note** The expectations over the seed and the observations are computed by backward induction (nested integration of the kernels), in $[0,\infty]$. $\min_{\mathcal K}L$ is $\inf L(\mathcal K)$, which is the minimum for compact nonempty $\mathcal K$ and continuous $L$. Conditions "conditional on previous queries and observations, and on $x_\tau$" are conditions on the kernels at every history.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Corollary 3.1, p.30 (PDF 32); §6.3, eqs. (55)–(57), pp.43–45 (PDF 45–47)

import Mathlib

namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory

/-! # Stochastic zeroth-order (convex) bandits: algorithms, environments, expected regret

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), Corollary 3.1, p.30
(PDF 32) and its use in §6.3, eq. (55)–(57), pp.43–45 (PDF 45–47).

An **algorithm** on a query space `X` draws a seed `ω` from `(Ω, P)` once; its `τ`-th query
(`τ = 0, 1, …`) is `query τ ω h ∈ X`, where `h : Fin τ → X × ℝ` lists the past (query,
observation) pairs. An **environment** is a sequence of Markov kernels: given the past pairs `h`
and the current query `x`, `ν τ (h, x)` is the conditional law of the observation. The noise
conditions of Corollary 3.1 ("conditional on previous queries and observations, and on `x_τ`")
are conditions on these kernels.

**Formalization Note.** The expectation over the seed and the observations is computed by
backward induction (nested integration of the kernels, then over the seed), in `ℝ≥0∞`, for
nonnegative quantities: `regret` is `E[∑_{τ<n} (L(x_τ) − min_𝒦 L)]` (the terms are
nonnegative when every query lies in `𝒦`), and `trajExp` is `E[f(trajectory)]` for a
nonnegative function `f` of the length-`n` trajectory; `multiExp` is the same for `M`
independent copies of the run (each with its own seed and observations). The query map is
jointly measurable in the seed and the past, and kernels are measurable by definition, so these
iterated integrals are the expectations of the process. `min_𝒦 L` is `sInf (L '' 𝒦)`, the minimum
when `𝒦` is compact and nonempty and `L` continuous on it. -/

/-- An adaptive randomized algorithm with query space `X` and seed space `Ω`. -/
structure BanditAlg (X Ω : Type) [MeasurableSpace X] [MeasurableSpace Ω] where
  /-- the query of step `τ`, given the seed and the past (query, observation) pairs -/
  query : (τ : ℕ) → Ω → (Fin τ → X × ℝ) → X
  measurable_query : ∀ τ, Measurable fun p : Ω × (Fin τ → X × ℝ) => query τ p.1 p.2

/-- An observation environment: the conditional law of the `τ`-th observation given the past
pairs and the current query. -/
abbrev ObsEnv (X : Type) [MeasurableSpace X] : Type :=
  (τ : ℕ) → Kernel ((Fin τ → X × ℝ) × X) ℝ

namespace BanditAlg

variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]

/-- Backward induction with `k` steps left from step `τ`: running cost `c` at every query, then
the terminal value `term` of the history reached. -/
noncomputable def go (alg : BanditAlg X Ω) (ν : ObsEnv X) (c : X → ENNReal)
    (term : (τ : ℕ) → (Fin τ → X × ℝ) → ENNReal) :
    (k τ : ℕ) → Ω → (Fin τ → X × ℝ) → ENNReal
  | 0, τ, _, h => term τ h
  | k + 1, τ, ω, h =>
    c (alg.query τ ω h) +
      ∫⁻ y, go alg ν c term k (τ + 1) ω
        (Fin.snoc (α := fun _ => X × ℝ) h (alg.query τ ω h, y)) ∂(ν τ (h, alg.query τ ω h))

/-- The expected regret of `n` queries, `E[∑_{τ<n} (L(x_τ) − min_{x ∈ 𝒦} L(x))]`. -/
noncomputable def regret (alg : BanditAlg X Ω) (ν : ObsEnv X) (P : Measure Ω) (n : ℕ)
    (L : X → ℝ) (K : Set X) : ENNReal :=
  ∫⁻ ω, alg.go ν (fun x => ENNReal.ofReal (L x - sInf (L '' K))) (fun _ _ => 0) n 0 ω
    Fin.elim0 ∂P

/-- The expectation `E[f(h)]` of a nonnegative function of the length-`n` trajectory
`h = ((x_0, Y_0), …, (x_{n−1}, Y_{n−1}))`. -/
noncomputable def trajExp (alg : BanditAlg X Ω) (ν : ObsEnv X) (P : Measure Ω) (n : ℕ)
    (f : (Fin n → X × ℝ) → ENNReal) : ENNReal :=
  ∫⁻ ω, alg.go ν (fun _ => 0)
    (fun τ h => if hτ : τ = n then f (fun i => h (Fin.cast hτ.symm i)) else 0) n 0 ω
    Fin.elim0 ∂P

/-- The expectation `E[f(h_0, …, h_{M−1})]` over `M` independent runs of length `n`. -/
noncomputable def multiExp (alg : BanditAlg X Ω) (ν : ObsEnv X) (P : Measure Ω) (n : ℕ) :
    (M : ℕ) → ((Fin M → Fin n → X × ℝ) → ENNReal) → ENNReal
  | 0, f => f Fin.elim0
  | M + 1, f => alg.trajExp ν P n fun t => multiExp alg ν P n M fun ts => f (Fin.cons t ts)

/-- Every query lies in `𝒦`. -/
def QueriesIn (alg : BanditAlg X Ω) (K : Set X) : Prop :=
  ∀ τ ω h, alg.query τ ω h ∈ K

end BanditAlg

/-- The environment's observations have conditional mean `L(x)` at every query `x ∈ 𝒦` (and are
integrable). -/
def ObsEnv.MeanOn {X : Type} [MeasurableSpace X] (ν : ObsEnv X) (L : X → ℝ) (K : Set X) :
    Prop :=
  (∀ τ, IsMarkovKernel (ν τ)) ∧
  ∀ τ h, ∀ x ∈ K, Integrable id (ν τ (h, x)) ∧ ∫ y, y ∂(ν τ (h, x)) = L x

/-- The environment's observations at queries `x ∈ 𝒦` lie in `S` almost surely. -/
def ObsEnv.ValuesIn {X : Type} [MeasurableSpace X] (ν : ObsEnv X) (K : Set X) (S : Set ℝ) :
    Prop :=
  ∀ τ h, ∀ x ∈ K, ν τ (h, x) Sᶜ = 0

end BilateralProfitRegular


