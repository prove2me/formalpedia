-- Prove2me | Definitions.Def_ConvexSDDP_Stoch_Selection
-- name    : ConvexSDDP_Stoch_Selection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:26.756536+00:00
-- url     : https://prove2.me/theorems/8c2c564c-445e-4e9a-baf5-d9895702979f
-- title:
--   Definition 1 and (23), pp. 14–15 — τ-admissible selection processes
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $(y^k)_{k\in\mathbb N}$ a selection process, $y^k_n(\omega)\in\{0,1\}$, with $y^k_n=1$ if node $n$ is selected at iteration $k$. For a positive integer $\tau$ put
--   $$\tilde y^k_n=\max\{y^{k\tau}_n,\,y^{k\tau+1}_n,\,\dots,\,y^{k\tau+\tau-1}_n\}\qquad\text{(23)},$$
--   and $\mathcal F_{k\tau-1}=\sigma\big((y^{k'})_{k'<k\tau}\big)$ (p. 21).
--
--   **Definition 1.** The process $(y^k)$ is **$\tau$-admissible** if
--   1. for every $m\in\mathcal N\setminus\mathcal L$, every $k\in\mathbb N$ and every $\kappa\in\{0,\dots,\tau-1\}$,
--   $$y^{k\tau+\kappa}_m=1\ \Longrightarrow\ \forall n\in a(m),\quad y^{k\tau}_n=y^{k\tau+1}_n=\dots=y^{k\tau+\kappa-1}_n=0;$$
--   2. for every $m\in\mathcal N\setminus\mathcal L$ the sequence $(\tilde y^k_m)_{k\in\mathbb N}$ is i.i.d., and every $\tilde y^k_m$ is independent of $\mathcal F_{k\tau-1}$;
--   3. $\mathbb P(\tilde y^k_n=1)>0$ for every $n\in\mathcal N\setminus\mathcal L$.
--
--   Property (1) makes the cuts of one block of $\tau$ iterations be computed backwards in the tree; (2) and (3) ensure every node is selected infinitely often, independently of the past. No independence across nodes at a fixed iteration is required.
--
--   **Formalization Note** Property (1) is required along every sample path. At $k=0$, $\mathcal F_{-1}$ is the trivial σ-algebra. Property (3) is stated for every $k$ (the page leaves $k$ free; by (2) it does not depend on $k$).
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, pp. 14–15, Definition 1 and (23); p. 21, definition of ℱ_{kτ−1}

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Stoch_Tree

namespace ConvexSDDP.Stoch

open StochasticProg.Multistage MeasureTheory ProbabilityTheory

variable {H : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- (23), p. 14: `ỹ^k_n = max{y^{kτ}_n, …, y^{kτ+τ-1}_n}`, i.e. `ỹ^k_n = 1` iff node `n` is
selected at some iteration of the block `kτ, …, kτ + τ - 1`. -/
def ytilde {N : Type*} (Y : ℕ → Ω → N → Bool) (τ k : ℕ) (n : N) (ω : Ω) : Bool :=
  decide (∃ κ < τ, Y (k * τ + κ) ω n = true)

/-- Definition 1 (i), p. 14, for one selection path `ys` (`ys k n = true` iff `y^k_n = 1`): if
the non-leaf node `m` is selected at iteration `kτ + κ` (`κ < τ`), then no ascendent of `m`
(including `m` itself) is selected at the iterations `kτ, …, kτ + κ - 1`. -/
def AdmissibleI (T : Tree H) (ys : ℕ → T.Node → Bool) (τ : ℕ) : Prop :=
  ∀ m, ¬ IsLeaf T m → ∀ k, ∀ κ < τ, ys (k * τ + κ) m = true →
    ∀ n ∈ asc T m, ∀ j < κ, ys (k * τ + j) n = false

/-- Definition 1, pp. 14–15: the selection process `(y^k)` (`Y k ω n = true` iff `y^k_n = 1`)
is *τ-admissible* for the positive integer `τ` if
(i) holds along every path;
(ii) for every non-leaf `m`, the sequence `(ỹ^k_m)_k` is i.i.d., and every `ỹ^k_m` is
     independent of `ℱ_{kτ-1} = σ(y^{k'} : k' < kτ)` (the trivial σ-algebra when `k = 0`);
(iii) `ℙ(ỹ^k_n = 1) > 0` for every non-leaf `n` and every `k`. -/
def IsAdmissible (T : Tree H) (P : Measure Ω) (Y : ℕ → Ω → T.Node → Bool) (τ : ℕ) : Prop :=
  0 < τ ∧
  (∀ ω, AdmissibleI T (fun k => Y k ω) τ) ∧
  (∀ m, ¬ IsLeaf T m →
    (iIndepFun (fun k ω => ytilde Y τ k m ω) P ∧
      ∀ k, IdentDistrib (fun ω => ytilde Y τ k m ω) (fun ω => ytilde Y τ 0 m ω) P P) ∧
    ∀ k, Indep (MeasurableSpace.comap (fun ω => ytilde Y τ k m ω) inferInstance)
      (⨆ j, ⨆ (_ : j < k * τ), MeasurableSpace.comap (Y j) inferInstance) P) ∧
  (∀ n, ¬ IsLeaf T n → ∀ k, 0 < P {ω | ytilde Y τ k n ω = true})

end ConvexSDDP.Stoch


