-- Prove2me | Definitions.Def_CBCLowerBound_EveryNorm_Chasing
-- name    : CBCLowerBound_EveryNorm_Chasing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:02.570672+00:00
-- url     : https://prove2.me/theorems/bfe8f760-a721-4c23-85fc-e902f9eb9477
-- title:
--   Convex body chasing in a normed space: bodies, online and randomized algorithms, cost, offline optimum, competitiveness
-- statement:
--   Let $X$ be a real normed space with norm $\|\cdot\|$ and let $x_0\in X$ be a start point. In **convex body chasing** an adversary reveals, one at a time, sets $K_1,\dots,K_T\subseteq X$, where the horizon $T\in\mathbb N$ is not known in advance.
--
--   1. A **body** is a nonempty closed convex subset of $X$.
--   2. A **deterministic online algorithm** started at $x_0$ assigns to every finite prefix $K_1,\dots,K_t$ of requests a point $x_t$, with $x_0$ for the empty prefix; the point depends only on the prefix. Whenever $K_1,\dots,K_t$ are bodies, $x_t\in K_t$.
--   3. Its **cost** on $\sigma=(K_1,\dots,K_T)$ is its total movement
--   $$\mathrm{Alg}(K_1,\dots,K_T)=\sum_{t=1}^{T}\|x_t-x_{t-1}\|.$$
--   4. The **offline optimum** is
--   $$\mathrm{Opt}(K_1,\dots,K_T)=\inf\Big\{\sum_{t=1}^T\|y_t-y_{t-1}\| : y_0=x_0,\ y_t\in K_t\ (1\le t\le T)\Big\}.$$
--   5. A **randomized online algorithm** is a probability space $(\Omega,P)$ together with a deterministic online algorithm for each seed $\omega\in\Omega$, such that each decision is a measurable function of $\omega$ (Borel $\sigma$-algebra on $X$). The seed is independent of the requests. Its cost on $\sigma$ is the expected movement $\mathbb E_\omega[\mathrm{Alg}_\omega(\sigma)]$, valued in $[0,\infty]$.
--   6. A randomized algorithm is **$R$-competitive** if $\mathbb E[\mathrm{Alg}(\sigma)]\le R\cdot\mathrm{Opt}(\sigma)$ for every finite sequence $\sigma$ of bodies. The competitive ratio $\mathrm{CR}(\mathrm{Alg})=\sup_\sigma \mathrm{Alg}(\sigma)/\mathrm{Opt}(\sigma)$ is the infimum of such $R$, so "$\mathrm{CR}\ge\rho$" means that every $R$ for which the algorithm is $R$-competitive satisfies $R\ge\rho$.
--
--   These are the objects of the goal theorem and of Proposition 9. Deterministic algorithms are the randomized algorithms with a one-point seed space.
--
--   **Formalization Note** A request sequence is a `List (Set X)`; `σ[t]` is $K_{t+1}$. The feasibility field of an algorithm is required only along sequences of bodies, so algorithms exist for every $X$ and $x_0$. The expected cost is a lower Lebesgue integral of the nonnegative cost, so it needs no integrability hypothesis. The offline optimum is a real infimum of a set that is nonempty for nonempty bodies and bounded below by $0$.
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.2, §1 (problem definition and CR(Alg)), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace CBCLowerBound.EveryNorm

/-! # Convex body chasing in a normed space (Christianson, STOC 2027 #674, §1, p.2)

Starting from `x₀`, an online algorithm receives nonempty closed convex sets `K₁, …, K_T`
(`T` unknown in advance); after seeing `K_t` it picks `x_t ∈ K_t` and pays `‖x_t − x_{t−1}‖`.
-/

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A **body** (request) of convex body chasing: a nonempty closed convex set (p.2). -/
def IsBody (K : Set X) : Prop :=
  K.Nonempty ∧ IsClosed K ∧ Convex ℝ K

/-- A **deterministic online algorithm** for convex body chasing started at `x₀`.
`pos l` is the point held after the requests `l = [K₁, …, K_t]` have been revealed; it depends
only on this prefix (online), and it is defined on every prefix (the horizon `T` is unknown).
Before any request the algorithm is at `x₀`. Whenever every revealed set is a body, the new
point lies in the newest body. -/
structure Algorithm (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (x₀ : X) where
  /-- The decision after the revealed prefix of requests. -/
  pos : List (Set X) → X
  /-- Before any request the algorithm sits at the start point. -/
  pos_nil : pos [] = x₀
  /-- Feasibility: the decision after `K_t` lies in `K_t` (for sequences of bodies). -/
  pos_mem : ∀ (l : List (Set X)) (K : Set X), (∀ K' ∈ l, IsBody K') → IsBody K →
    pos (l ++ [K]) ∈ K

namespace Algorithm

variable {x₀ : X}

/-- The total movement `∑_{t=1}^T ‖x_t − x_{t−1}‖` of a deterministic algorithm on the request
sequence `σ = [K₁, …, K_T]`, where `x_t = pos (K₁ … K_t)`. -/
noncomputable def cost (A : Algorithm X x₀) (σ : List (Set X)) : ℝ :=
  ∑ t ∈ Finset.range σ.length, ‖A.pos (σ.take (t + 1)) - A.pos (σ.take t)‖

end Algorithm

/-- The **offline optimum** `Opt(K₁, …, K_T)`: the infimum of `∑_{t=1}^T ‖y_t − y_{t−1}‖` over all
offline trajectories with `y₀ = x₀` and `y_t ∈ K_t` for `1 ≤ t ≤ T` (here `σ[t]` is `K_{t+1}`).
For a sequence of nonempty sets the set of costs is nonempty and bounded below by `0`. -/
noncomputable def opt (x₀ : X) (σ : List (Set X)) : ℝ :=
  sInf {c : ℝ | ∃ y : ℕ → X, y 0 = x₀ ∧ (∀ (t : ℕ) (ht : t < σ.length), y (t + 1) ∈ σ[t]) ∧
    c = ∑ t ∈ Finset.range σ.length, ‖y (t + 1) - y t‖}

/-- A **randomized online algorithm** started at `x₀`: a probability space `(Ω, P)` and, for each
random seed `ω`, a deterministic online algorithm, such that every decision is a measurable
function of the seed (Borel σ-algebra on `X`). The seed is drawn independently of the requests
(oblivious adversary). A deterministic algorithm is the case of a one-point `Ω`. -/
structure RandomizedAlgorithm (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (x₀ : X) where
  /-- The seed space. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The law of the seed. -/
  P : Measure Ω
  /-- The law of the seed is a probability measure. -/
  [isProb : IsProbabilityMeasure P]
  /-- The deterministic algorithm run with seed `ω`. -/
  alg : Ω → Algorithm X x₀
  /-- Each decision is a measurable function of the seed. -/
  measurable_pos : ∀ l : List (Set X), @Measurable Ω X mΩ (borel X) (fun ω => (alg ω).pos l)

namespace RandomizedAlgorithm

variable {x₀ : X}

/-- The expected total movement `E_ω[Alg(K₁, …, K_T)]` (a lower Lebesgue integral of a
nonnegative cost, valued in `[0, ∞]`). -/
noncomputable def expCost (A : RandomizedAlgorithm X x₀) (σ : List (Set X)) : ℝ≥0∞ :=
  letI := A.mΩ
  ∫⁻ ω, ENNReal.ofReal ((A.alg ω).cost σ) ∂A.P

/-- `A` is **`R`-competitive**: on every finite sequence of bodies,
`E[Alg(K₁, …, K_T)] ≤ R · Opt(K₁, …, K_T)` (no additive constant, as in the definition of
`CR(Alg)` on p.2). The competitive ratio `CR(A)` is the infimum of such `R`, so
"`CR(A) ≥ ρ`" says that every `R` for which `A` is `R`-competitive satisfies `ρ ≤ R`. -/
def IsCompetitive (A : RandomizedAlgorithm X x₀) (R : ℝ) : Prop :=
  ∀ σ : List (Set X), (∀ K ∈ σ, IsBody K) → A.expCost σ ≤ ENNReal.ofReal (R * opt x₀ σ)

end RandomizedAlgorithm

end CBCLowerBound.EveryNorm


