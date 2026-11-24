-- Prove2me | Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_LinModel
-- name    : RiskAverseSDDP_Subdiff_Supplement_LinModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:29:34.202356+00:00
-- url     : https://prove2.me/theorems/a7669fb5-5de5-4321-9758-19210e535fa4
-- title:
--   (5.35)–(5.36) and (H2'), pp. 15, 17 — the risk-averse multistage stochastic linear program without relatively complete recourse
-- statement:
--   This file fixes the model of §5 of Guigues (2016): a risk-averse multistage stochastic **linear** program in which the relatively complete recourse assumption is not made.
--
--   **Data.** There are $T$ stages $t=1,\dots,T$, decisions $x_t\in\mathbb R^n$, a given initial decision $x_0$, and a history $x_{1:t}=(x_1,\dots,x_t)$ is identified with the vector $[x_1;\dots;x_t]\in\mathbb R^{nt}$ with its Euclidean norm. Under the interstage independence (H1), $\xi_1$ is deterministic and, for $t=2,\dots,T$, $\xi_t$ takes $M$ values $\xi_{t,1},\dots,\xi_{t,M}$ with probabilities $\Phi_{t,j}$. The realization $\xi_{t,j}$ carries a cost vector $\Psi_{t,j}\in\mathbb R^{nt}$, matrices $A_{t,\tau,j}$ ($\tau=0,\dots,t$) and a right-hand side $b_{t,j}\in\mathbb R^q$. Each stage also carries a convex set $\mathcal P_t$ of probability densities, which defines the risk measure $\rho_t(Z)=\sup_{p\in\mathcal P_t}\sum_j p_j\Phi_{t,j}Z_j$ of (3.13).
--
--   **The program (5.35)–(5.36).** The feasible sets are
--   $$X_t(x_{0:t-1},\xi_{t,j})=\Big\{x_t\in\mathbb R^n_+:\ \sum_{\tau=0}^{t}A_{t,\tau,j}x_\tau=b_{t,j}\Big\}.$$
--   The recourse functions are $\mathcal Q_{T+1}\equiv0$ and, for $t=2,\dots,T$, $\mathcal Q_t(x_{1:t-1})=\rho_t\big(\mathfrak Q_t(x_{1:t-1},\xi_t)\big)$ with
--   $$\mathfrak Q_t(x_{1:t-1},\xi_{t,j})=\inf\big\{\Psi_{t,j}^\top x_{1:t}+\mathcal Q_{t+1}(x_{1:t}):\ x_t\in X_t(x_{0:t-1},\xi_{t,j})\big\}.$$
--   The first-stage problem is $\inf\{\Psi_1^\top x_1+\mathcal Q_2(x_1):\ x_1\in X_1(x_0,\xi_1)\}$, with optimal value $\mathcal Q_1(x_0)$. All values are in $\mathbb R\cup\{\pm\infty\}$, and an infimum over an empty set is $+\infty$. This is the instance of the general program (3.9) with $\mathcal X_t=\mathbb R^n_+$, the linear cost $f_t(x_{1:t},\Psi_{t,j})=\Psi_{t,j}^\top x_{1:t}$ and no nonlinear constraints, so the recourse functions, first-stage value and first-stage optimality of the published model `RiskAverseSDDP.Convergence.Model` apply unchanged.
--
--   **Assumption (H2').** For every $t=1,\dots,T$, every realization $(\tilde\xi_1,\dots,\tilde\xi_t)$ of $(\xi_1,\dots,\xi_t)$ and every sequence of decisions $x_{0:t-1}$ that is feasible on that scenario, i.e. $x_\tau\in X_\tau(x_{0:\tau-1},\tilde\xi_\tau)$ for $\tau=1,\dots,t-1$, the set $X_t(x_{0:t-1},\tilde\xi_t)$ is bounded and nonempty.
--
--   These objects are the setting of Theorem 5.1.
--
--   **Formalization Note** `LinModel.toModel` builds the published `Model` with $p=0$ nonlinear constraints (the constraint function has the empty codomain `Fin 0`). Stage 1 uses realization index `0`. A scenario is a map `w : ℕ → Fin M` giving the realization index at each stage $t\ge2$, and `scenRlz w 1 = 0`. `Hist.take x i` is the prefix $x_{1:i}$ of $x_{1:s}$. Assumption (H2') ranges over all scenarios `w`, which covers every realization because every $\Phi_{t,j}>0$.
--
--   The structure stores raw data. Positivity and normalization of probabilities, convexity and nonemptiness of the risk sets are imposed by `toModel.Standing` in the theorem, rather than by the structure itself.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 15, (5.35)–(5.36), and p. 17, Assumption (H2') of Theorem 5.1

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model

namespace RiskAverseSDDP.Subdiff.Supplement

open RiskAverseSDDP.Convergence

/-- The data of the risk-averse multistage stochastic linear program (5.35)–(5.36), p. 15, under
the interstage independence (H1), with `T` stages, decisions in `ℝⁿ`, `M` realizations of `ξ_t`
per stage `t = 2, …, T` and `q` linear equality constraints per stage. Stages carry the paper's
numbering `t = 1, …, T` and realizations are indexed by `j ∈ Fin M`; stage 1 is deterministic and
uses the realization `j = 0`.
* `x0 ∈ ℝⁿ` the given initial decision `x_0`;
* `Ψ t j ∈ ℝ^{nt}` the cost vector `Ψ_{t,j}` of the linear cost `Ψ_{t,j}ᵀ x_{1:t}`;
* `A t j τ` the matrix `A_{t,τ,j}` (`τ = 0, …, t`, as a linear map) and `b t j` the right-hand
  side `b_{t,j}`;
* `Φ t j = ℙ(ξ_t = ξ_{t,j})`;
* `Prisk t ⊆ ℝᴹ` the set `𝒫_t` of the dual representation (3.13) of `ρ_t`. -/
structure LinModel (T n M q : ℕ) where
  x0 : EuclideanSpace ℝ (Fin n)
  Ψ : (t : ℕ) → Fin M → Hist n t
  A : (t : ℕ) → Fin M → Fin (t + 1) → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin q))
  b : ℕ → Fin M → EuclideanSpace ℝ (Fin q)
  Φ : ℕ → Fin M → ℝ
  Prisk : ℕ → Set (Fin M → ℝ)

namespace LinModel

variable {T n M q : ℕ}

/-- The linear program (5.35)–(5.36) as an instance of the risk-averse program (3.9): the sets
`𝒳_t = ℝⁿ₊` (§5 replaces (H2)-1) by this), the linear cost
`f_t(x_{1:t}, Ψ_{t,j}) = Ψ_{t,j}ᵀ x_{1:t}`, no nonlinear constraints (`p = 0`), and the same
matrices, right-hand sides, probabilities and risk sets. Its feasible sets are
`X_t(x_{0:t-1}, ξ_{t,j}) = {x_t ≥ 0 : Σ_{τ=0}^t A_{t,τ,j} x_τ = b_{t,j}}`, and its recourse
functions `Model.Q` are those of (5.35) (with `𝒬_{T+1} ≡ 0`), with value `+∞` at states that
have no feasible decision. -/
noncomputable def toModel (L : LinModel T n M q) : Model T n M q 0 where
  x0 := L.x0
  Xc := fun _ => {y | ∀ i, 0 ≤ y i}
  f := fun t j x => ((inner ℝ (L.Ψ t j) x : ℝ) : EReal)
  g := fun _ _ _ _ i => i.elim0
  A := L.A
  b := L.b
  Φ := L.Φ
  Prisk := L.Prisk

end LinModel

/-- The first `i` decisions `x_{1:i}` of a history `x_{1:s}`, `i ≤ s`. -/
def Hist.take {n s : ℕ} (x : Hist n s) (i : ℕ) (h : i ≤ s) : Hist n i :=
  WithLp.toLp 2 (fun l : Fin i => x (Fin.castLE h l))

/-- The realization index at stage `t` of the scenario `w` (`w t` the index of `ξ_t` for
`t ≥ 2`): stage 1 is deterministic and has index `0`. -/
def scenRlz {M : ℕ} [NeZero M] (w : ℕ → Fin M) (t : ℕ) : Fin M :=
  if t = 1 then 0 else w t

namespace LinModel

variable {T n M q : ℕ}

/-- Assumption (H2'), p. 17: for every `t = s + 1 = 1, …, T`, every realization
`(ξ̃_1, …, ξ̃_t)` (the scenario `w`) and every sequence of decisions `x_{1:t-1}` that is feasible
on that scenario, i.e. `x_τ ∈ X_τ(x_{0:τ-1}, ξ̃_τ)` for `τ = 1, …, t - 1`, the set
`X_t(x_{0:t-1}, ξ̃_t)` is bounded and nonempty. -/
def H2' [NeZero M] (L : LinModel T n M q) : Prop :=
  ∀ s, s < T → ∀ w : ℕ → Fin M, ∀ x : Hist n s,
    (∀ i : Fin s, x i ∈ L.toModel.feas i.val (scenRlz w (i.val + 1)) (Hist.take x i.val i.2.le)) →
      Bornology.IsBounded (L.toModel.feas s (scenRlz w (s + 1)) x) ∧
        (L.toModel.feas s (scenRlz w (s + 1)) x).Nonempty

end LinModel

end RiskAverseSDDP.Subdiff.Supplement


