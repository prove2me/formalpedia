-- Prove2me | Definitions.Def_BayesProphet_MultiSec_Supplement_Packing
-- name    : BayesProphet_MultiSec_Supplement_Packing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:07:14.454815+00:00
-- url     : https://prove2.me/theorems/b83efb25-90ba-4c8c-abc1-9ef181dc5872
-- title:
--   Online Packing, its LPs and the Fluid Bayes Selector (Sec. 2.1, Eq. (4), Algorithm 2, Proposition 2)
-- statement:
--   This file defines Online Packing, the packing LP and the Fluid Bayes Selector of Algorithm 2.
--
--   **Model.** There are $d$ resources and $n$ types. A consumption matrix $A\in\mathbb N^{d\times n}$ and rewards $r\in\mathbb R^n$ are given: serving a type-$j$ request uses $a_{ij}$ units of each resource $i$ and earns $r_j$. The state is the budget vector $b\in\mathbb N^d$; accepting the arrival $\theta^t=j$ is feasible iff $A_j\le b$ (componentwise) and lowers the budget to $b-A_j$; rejecting earns nothing. Offline's value, Online's value and the regret $\mathrm{Reg}=V^{\mathrm{off}}(T,B)-V^{\mathrm{on}}(T,B)$ are those of the published generic online decision problem. $r_{\max}=\max_j r_j$.
--
--   **Packing LP** (Eq. (4), Proposition 2). For $b\in\mathbb R^d$ and $y\in\mathbb R^n$,
--   $$P(y):\quad \max\{r'x:\ Ax\le b,\ 0\le x\le y\}.$$
--   A real $\kappa$ is an **LP Lipschitz constant** for $A$ w.r.t. a norm $\mu$ on $\mathbb R^n$ if for every $b\in\mathbb R^d$, every $r\in\mathbb R^n$, all $y,\hat y\in\mathbb R^n_{\ge0}$ and every optimal solution $x$ of $P(y)$ there is an optimal solution $\hat x$ of $P(\hat y)$ with $\|x-\hat x\|_\infty\le\kappa\|y-\hat y\|_\mu$.
--
--   **Fluid Bayes Selector** (Algorithm 2). With $t$ periods to go and budget $B^t$, let $X^t$ be any optimal solution of the fluid LP $(P_t)$: $\max r'x$ s.t. $Ax\le B^t$, $x\le\mathbb E[Z(t)]$, $x\ge0$. On arrival $\theta^t=j$, accept iff $X^t_j\ge\mathbb E[Z_j(t)]/2$ and $A_j\le B^t$; otherwise reject. The expected regret is $\mathbb E[\mathrm{Reg}]$ under the arrival law.
--
--   **Formalization Note** An action names the type it accepts (`some k`; `none` rejects), and it does nothing if a different type arrives; this encodes the paper's arrival-dependent feasibility $A_{\theta^t}\le B^t$ in the state-only feasible set of the published `OnlineProblem` without changing Offline's value. The selection $X$ is a function of $(t,b)$ and is only required to pick some optimizer (ties arbitrary). The policy uses the unconditional mean $\mathbb E[Z(t)]$ of the given law.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 6 (Online Packing), p. 17 (Eq. (4), Algorithm 2), p. 18 (r_max), p. 20 (Proposition 2)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary
import Definitions.Def_BayesProphet_MultiSec_Supplement_Arrivals

namespace BayesProphet.MultiSec.Supplement

open BayesProphet.MultiSec

/-- Feasible set of the packing LP `P(y) = max{r'x : Ax ≤ b, 0 ≤ x ≤ y}` (Proposition 2, p. 20; the
fluid LP `(P_t)` of Eq. (4), p. 17, is `y = E[Z(t)]`, `b = B^t`), for a consumption matrix
`A ∈ ℕ^{d×n}`. -/
def packFeas {d n : ℕ} (A : Fin d → Fin n → ℕ) (b : Fin d → ℝ) (y : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | (∀ i, ∑ j, (A i j : ℝ) * x j ≤ b i) ∧ ∀ j, 0 ≤ x j ∧ x j ≤ y j}

/-- Optimal solutions of the packing LP `P(y)` with objective `r'x`. -/
def packOpt {d n : ℕ} (A : Fin d → Fin n → ℕ) (r : Fin n → ℝ) (b : Fin d → ℝ)
    (y : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ packFeas A b y ∧ ∀ x' ∈ packFeas A b y, ∑ j, r j * x' j ≤ ∑ j, r j * x j}

/-- `κ` is an LP Lipschitz constant for `A` w.r.t. the norm `μ` (the property of Proposition 2,
p. 20): for every right-hand side `b ∈ ℝ^d`, every objective `r ∈ ℝ^n`, all `y, ŷ ∈ ℝ^n_{≥0}` and
every optimal solution `x` of `P(y)` there is an optimal solution `x̂` of `P(ŷ)` with
`‖x − x̂‖_∞ ≤ κ ‖y − ŷ‖_μ`. (`‖·‖` on `Fin n → ℝ` is the sup norm.) -/
def IsLPLipschitzConst {d n : ℕ} (A : Fin d → Fin n → ℕ) (μ : (Fin n → ℝ) → ℝ) (κ : ℝ) :
    Prop :=
  ∀ (b : Fin d → ℝ) (r : Fin n → ℝ) (y y₂ : Fin n → ℝ), (∀ j, 0 ≤ y j) → (∀ j, 0 ≤ y₂ j) →
    ∀ x ∈ packOpt A r b y, ∃ x₂ ∈ packOpt A r b y₂, ‖x - x₂‖ ≤ κ * μ (y - y₂)

/-- Online Packing (Sec. 2.1, p. 6; Sec. 4, p. 17) as an online decision problem: the state is the
budget vector `b ∈ ℕ^d`; the action `some k` accepts the arrival if it is of type `k` (consuming the
column `A_k` and earning `r_k`) and does nothing otherwise; `none` rejects. Accepting type `k` is
feasible iff `A_k ≤ b`. (Naming the accepted type in the action encodes the paper's arrival-dependent
feasibility `A_{θ^t} ≤ B^t` in a state-only feasible set; Offline's value is unchanged.) -/
def packingProblem {d n : ℕ} (A : Fin d → Fin n → ℕ) (r : Fin n → ℝ) :
    OnlineProblem (Fin d → ℕ) (Fin n) (Option (Fin n)) where
  trans a b j := match a with
    | some k => if k = j then b - (fun i => A i k) else b
    | none => b
  reward a _ j := match a with
    | some k => if k = j then r k else 0
    | none => 0
  feasible b := {a | ∀ k, a = some k → ∀ i, A i k ≤ b i}

/-- The Fluid Bayes Selector for Online Packing (Algorithm 2, p. 17), run with a selection `X t b`
of solutions of the fluid LP `(P_t)` at budget `b`: on arrival `θ^t = j`, accept iff
`X^t_j ≥ E[Z_j(t)]/2` and it is feasible (`A_j ≤ B^t`); otherwise reject. -/
noncomputable def fluidBayesPacking {d n T : ℕ} [NeZero n] (A : Fin d → Fin n → ℕ)
    (w : (Fin T → Fin n) → ℝ) (X : ℕ → (Fin d → ℕ) → Fin n → ℝ) :
    Policy (Fin d → ℕ) (Fin n) (Option (Fin n)) :=
  fun t θ b => by
    classical exact
      if meanCount w t (θ t) / 2 ≤ X t b (θ t) ∧ ∀ i, A i (θ t) ≤ b i then some (θ t) else none

/-- `X` selects, at every time-to-go `t` and budget `b ∈ ℕ^d`, an optimal solution of the fluid LP
`(P_t)` of Eq. (4): `max r'x s.t. Ax ≤ b, x ≤ E[Z(t)], x ≥ 0` (any optimizer; uniqueness is not
required). -/
def IsPackingFluidSelection {d n T : ℕ} [NeZero n] (A : Fin d → Fin n → ℕ) (r : Fin n → ℝ)
    (w : (Fin T → Fin n) → ℝ) (X : ℕ → (Fin d → ℕ) → Fin n → ℝ) : Prop :=
  ∀ t b, X t b ∈ packOpt A r (fun i => (b i : ℝ)) (meanVec w t)

/-- Expected regret `E[V^off − V^on]` of Algorithm 2 with `T` periods to go and initial budget `B`,
under the arrival law `w`. -/
noncomputable def packingExpectedRegret {d n T : ℕ} [NeZero n] (A : Fin d → Fin n → ℕ)
    (r : Fin n → ℝ) (w : (Fin T → Fin n) → ℝ) (X : ℕ → (Fin d → ℕ) → Fin n → ℝ)
    (B : Fin d → ℕ) : ℝ :=
  expectL w (fun θ => (packingProblem A r).regret (fluidBayesPacking A w X) T B θ)

/-- `r_max = max_j r_j` (p. 18). -/
noncomputable def packRmax {n : ℕ} [NeZero n] (r : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty r

end BayesProphet.MultiSec.Supplement


