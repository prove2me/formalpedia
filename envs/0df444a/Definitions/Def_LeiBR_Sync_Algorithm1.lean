-- Prove2me | Definitions.Def_LeiBR_Sync_Algorithm1
-- name    : LeiBR_Sync_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:09:33.407715+00:00
-- url     : https://prove2.me/theorems/a4e7c20f-6db1-4dfd-ad12-0aebd4c615f6
-- title:
--   Algorithm 1 (synchronous inexact proximal BR) with condition (8), the inner SA loop (SA_{i,k}), the $\sigma$-fields $\mathcal F_k$ and $Q_i$
-- statement:
--   **Algorithm 1** (synchronous inexact proximal best response). Start from a deterministic $x_0=y_0\in X$ and deterministic accuracies $\alpha_{i,k}\ge0$. At major iteration $k$, every player $i$ computes $x_{i,k+1}\in X_i$ with
--   $$\mathbb E\big[\|x_{i,k+1}-\hat x_i(y_k)\|^2\,\big|\,\mathcal F_k\big]\le\alpha_{i,k}^2\quad\text{a.s.},\tag{8}$$
--   and sets $y_{k+1}=x_{k+1}$. Here $\mathcal F_k$ is the $\sigma$-field of the information used up to the update of $x_k$, and $x_k$ is $\mathcal F_k$-measurable.
--
--   **Inner stochastic approximation loop.** At major iteration $k$, player $i$ takes $j_{i,k}$ projected stochastic gradient steps
--   $$z_{i,t+1}=\Pi_{X_i}\Big[z_{i,t}-\gamma_t\big(\nabla_{x_i}\psi_i(z_{i,t},y_{-i,k};\xi^t_{i,k})+\mu(z_{i,t}-y_{i,k})\big)\Big],\qquad z_{i,1}=x_{i,k},\quad \gamma_t=\frac1{\mu(t+1)},\tag{SA$_{i,k}$}$$
--   and sets $x_{i,k+1}=z_{i,j_{i,k}}$. With $\xi_{i,k}=(\xi^1_{i,k},\dots,\xi^{j_{i,k}}_{i,k})$ and $\xi^{[t]}_{i,k}=(\xi^1_{i,k},\dots,\xi^t_{i,k})$, the information fields are
--   $$\mathcal F_k=\sigma\{x_0,\ \xi_{i,l},\ i\in\mathcal N,\ 0\le l\le k-1\},\qquad \sigma\{\mathcal F_k,\xi^{[t-1]}_{i,k}\}.$$
--   Finally $Q_i=2M_i^2/\mu^2+2D_{X_i}^2$, where $D_{X_i}=\sup\{\|x_i-x_i'\|:x_i,x_i'\in X_i\}$ is the diameter (16).
--
--   Algorithm 1 is the paper's synchronous scheme; the abstract form (any iterates satisfying (8)) carries the rate result, and the concrete form with (SA$_{i,k}$) carries the complexity result.
--
--   **Formalization Note** `IsAlg1` is the abstract scheme for a given filtration. `saIter` is the inner loop with $z_t$ at index $t\ge1$ (index $0$ is unused), `syncSA` is the concrete Algorithm 1 driven by the samples `ξs k i t` $=\xi^t_{i,k}$, and `saZ` gives $z_{i,t}$. `infoField` and `innerField` build $\mathcal F_k$ and $\sigma\{\mathcal F_k,\xi^{[t-1]}_{i,k}\}$ from the samples; the deterministic $x_0$ contributes nothing. $\Pi_{X_i}$ is passed as a map and tied to the projection in the theorems.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 6, Algorithm 1 and (8); p. 8, (16); p. 10, (SA_{i,k}), F_k, Lemma 3 (Q_i); p. 12, proof of Theorem 1

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame

open MeasureTheory

namespace LeiBR.Sync

variable {N : ℕ} {n : Fin N → ℕ}

/-- Algorithm 1 (p. 6), the synchronous inexact proximal BR scheme, as an abstract scheme:
`x k ω` is the profile `x_k` (and `y_k = x_k`, step (2)) on the outcome `ω`. The initial point is
a deterministic `x0 ∈ X`; every iterate lies in `X`; `x_k` is measurable with respect to the
information `σ`-field `F_k`; and (8) holds with the deterministic accuracies `α i k`:
`E[‖x_{i,k+1} - x̂_i(y_k)‖² | F_k] ≤ α_{i,k}²` a.s. -/
def IsAlg1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (F : Filtration ℕ mΩ)
    (X : ∀ i : Fin N, Set (Strat n i)) (xhat : Profile n → Profile n) (α : Fin N → ℕ → ℝ)
    (x0 : Profile n) (x : ℕ → Ω → Profile n) : Prop :=
  x0 ∈ stratSet X ∧ (∀ ω, x 0 ω = x0) ∧ (∀ k ω, x k ω ∈ stratSet X) ∧
  (∀ k, Measurable[F k] (x k)) ∧
  ∀ k (i : Fin N),
    P[fun ω => ‖x (k + 1) ω i - xhat (x k ω) i‖ ^ 2 | F k] ≤ᵐ[P] fun _ => α i k ^ 2

/-- The projected stochastic-gradient inner loop (SA_{i,k}) (p. 10) for one player at one major
iteration, with `γ_t = 1/(μ(t+1))`: `saIter proj G μ y_i ξ t = z_t` for `t ≥ 1`, where `z_1 = y_i`
(`= x_{i,k}`) and `z_{t+1} = Π[z_t - γ_t (G(z_t, ξ^t) + μ(z_t - y_i))]`. Here `G z s` is the
sampled partial gradient `∇_{x_i}ψ_i(z, y_{-i,k}; s)`. Index `0` is unused and set to `y_i`. -/
noncomputable def saIter {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (G : E → S → E) (μ : ℝ) (yi : E) (ξ : ℕ → S) : ℕ → E
  | 0 => yi
  | 1 => yi
  | t + 2 => proj (saIter proj G μ yi ξ (t + 1) - (1 / (μ * ((t : ℝ) + 2))) •
      (G (saIter proj G μ yi ξ (t + 1)) (ξ (t + 1)) + μ • (saIter proj G μ yi ξ (t + 1) - yi)))

/-- Algorithm 1 with the inner loop (SA_{i,k}): `x_0 = x0` and, at major iteration `k`, player
`i` runs `j i k` steps of (SA_{i,k}) from `z_{i,1} = x_{i,k}` with the samples
`ξ^t_{i,k} = ξs k i t ω` and sets `x_{i,k+1} = z_{i, j_{i,k}}`. -/
noncomputable def syncSA {Ω : Type*} {d : ℕ} (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (μ : ℝ)
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (x0 : Profile n) :
    ℕ → Ω → Profile n
  | 0 => fun _ => x0
  | k + 1 => fun ω i =>
      saIter (proj i) (fun z s => gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i z) s) μ
        (syncSA proj gψ μ j ξs x0 k ω i) (fun t => ξs k i t ω) (j i k)

/-- The inner iterate `z_{i,t}` of (SA_{i,k}) at major iteration `k` (`t ≥ 1`). -/
noncomputable def saZ {Ω : Type*} {d : ℕ} (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (μ : ℝ)
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (x0 : Profile n)
    (k : ℕ) (i : Fin N) (t : ℕ) (ω : Ω) : Strat n i :=
  saIter (proj i) (fun z s => gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i z) s) μ
    (syncSA proj gψ μ j ξs x0 k ω i) (fun t => ξs k i t ω) t

/-- `F_k = σ{x_0, ξ_{i,l}, i ∈ N, 0 ≤ l ≤ k-1}` (p. 10), with `ξ_{i,l} = (ξ^1_{i,l}, …,
ξ^{j_{i,l}}_{i,l})`; the initial point is deterministic and contributes nothing. -/
noncomputable def infoField {Ω : Type*} {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (k : ℕ) : MeasurableSpace Ω :=
  ⨆ (l : ℕ) (_ : l < k) (i : Fin N) (t : ℕ) (_ : 1 ≤ t ∧ t ≤ j i l),
    MeasurableSpace.comap (ξs l i t) inferInstance

/-- `σ{F_k, ξ^{[t-1]}_{i,k}}` (p. 10), with `ξ^{[t-1]}_{i,k} = (ξ^1_{i,k}, …, ξ^{t-1}_{i,k})`. -/
noncomputable def innerField {Ω : Type*} {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (k : ℕ) (i : Fin N) (t : ℕ) :
    MeasurableSpace Ω :=
  infoField j ξs k ⊔
    ⨆ (s : ℕ) (_ : 1 ≤ s ∧ s < t), MeasurableSpace.comap (ξs k i s) inferInstance

/-- `Q_i = 2M_i²/μ² + 2D²_{X_i}` (Lemma 3), with the diameter `D_{X_i}` of (16). -/
noncomputable def Qconst (X : ∀ i : Fin N, Set (Strat n i)) (M : Fin N → ℝ) (μ : ℝ)
    (i : Fin N) : ℝ :=
  2 * M i ^ 2 / μ ^ 2 + 2 * Metric.diam (X i) ^ 2

end LeiBR.Sync


