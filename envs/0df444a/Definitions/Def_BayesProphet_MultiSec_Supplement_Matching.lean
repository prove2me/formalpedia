-- Prove2me | Definitions.Def_BayesProphet_MultiSec_Supplement_Matching
-- name    : BayesProphet_MultiSec_Supplement_Matching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:09:34.64915+00:00
-- url     : https://prove2.me/theorems/c6acb3cb-9827-4cf6-8c1e-39d3eefc8763
-- title:
--   Online Matching, its LPs (Eqs. (13), (15)) and the Fluid Bayes Selector (Algorithm 3)
-- statement:
--   This file defines Online Matching, the matching LPs and Algorithm 3.
--
--   **Model** (Sec. 2.1, Sec. 5). There are $d$ resources and $n$ types, an adjacency matrix $A\in\{0,1\}^{d\times n}$ and rewards $r\in\mathbb R^{d\times n}_{\ge0}$; $S_j=\{i\in[d]:a_{ij}=1\}$. A fictitious resource $d+1$ with initial budget $T$ represents rejection. The state is $b\in\mathbb N^{d+1}$; matching the arrival $\theta^t=j$ to resource $i$ needs $b_i\ge1$, uses one unit of $i$ and earns $r_{ij}a_{ij}$ (zero for $i=d+1$). The initial state is $(B,T)$. $r_{\max}=\max_{i,j}r_{ij}a_{ij}$.
--
--   **Offline's LP** (Eq. (13)). For $z\in\mathbb R^n$ and $b\in\mathbb R^d$,
--   $$P[z,b]:\quad\max\sum_{i,j}x_{ij}r_{ij}a_{ij}\ \text{ s.t. }\ \sum_j x_{ij}\le b_i\ (i\in[d]),\ \ \sum_{i\in[d]}x_{ij}\le z_j\ (j\in[n]),\ \ x\ge0.$$
--   **Fluid LP** (Eq. (15)). For $b\in\mathbb R^{d+1}$, $(P_t)$ maximizes the same objective subject to $\sum_j x_{ij}\le b_i$ for $i\in[d+1]$, $\sum_{i\in[d+1]}x_{ij}=\mathbb E[Z_j(t)]$ for all $j$, $x\ge0$.
--
--   **Fluid Bayes Selector** (Algorithm 3). With $t$ periods to go and budget $B^t$, let $X^t$ be an optimal solution of $(P_t)$ and, on arrival $\theta^t=j$, let $K\in\arg\max\{X^t_{ij}:i\in[d+1]\}$ (ties arbitrary); match $j$ to $K$ and set $B^{t-1}_K=B^t_K-1$.
--
--   **Formalization Note** The adjacency matrix appears only in the objective, as in the paper. The fictitious resource is Lean index `Fin.last d`. The selection $X$ is required to be optimal whenever $(P_t)$ is feasible. Algorithm 3 has no feasibility test; the Lean policy sends the arrival to the fictitious resource if $B^t_K=0$. This branch is never taken on a sequence of positive probability (then $X^t_{Kj}\ge\mathbb E[Z_j(t)]/(d+1)>0$ forces $B^t_K>0$), so the expected regret is the paper's.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 6 (Online Matching), p. 23 (Eq. (13)), p. 24 (Eq. (15)), p. 25 (Algorithm 3)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary
import Definitions.Def_BayesProphet_MultiSec_Supplement_Arrivals

namespace BayesProphet.MultiSec.Supplement

open BayesProphet.MultiSec

/-- The `0/1` adjacency entry `a_{ij}` of the matching instance (`adj i j = true` iff `a_{ij} = 1`). -/
def adjR {d n : ℕ} (adj : Fin d → Fin n → Bool) (i : Fin d) (j : Fin n) : ℝ :=
  if adj i j then 1 else 0

/-- `|S_j| = #{i ∈ [d] : a_{ij} = 1}` (p. 23). -/
def degree {d n : ℕ} (adj : Fin d → Fin n → Bool) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => adj i j = true)).card

/-- Feasible set of Offline's matching LP `P[z, b]` (Eq. (13), p. 23) with `z ∈ ℝ^n`, `b ∈ ℝ^d`:
`Σ_j x_{ij} ≤ b_i` for every resource `i`, `Σ_i x_{ij} ≤ z_j` for every type `j`, `x ≥ 0`. -/
def matchFeas {d n : ℕ} (z : Fin n → ℝ) (b : Fin d → ℝ) : Set (Fin d → Fin n → ℝ) :=
  {x | (∀ i, ∑ j, x i j ≤ b i) ∧ (∀ j, ∑ i, x i j ≤ z j) ∧ ∀ i j, 0 ≤ x i j}

/-- Optimal solutions of `P[z, b]` (Eq. (13)): maximize `Σ_{i,j} x_{ij} r_{ij} a_{ij}` over
`matchFeas z b` (the adjacency matrix appears only in the objective). -/
def matchOpt {d n : ℕ} (adj : Fin d → Fin n → Bool) (r : Fin d → Fin n → ℝ) (z : Fin n → ℝ)
    (b : Fin d → ℝ) : Set (Fin d → Fin n → ℝ) :=
  {x | x ∈ matchFeas z b ∧ ∀ x' ∈ matchFeas z b,
    ∑ i, ∑ j, x' i j * r i j * adjR adj i j ≤ ∑ i, ∑ j, x i j * r i j * adjR adj i j}

/-- Reward of matching type `j` to resource `i ∈ [d+1]`: `r_{ij} a_{ij}` for a real resource
`i ∈ [d]` (Lean indices `0, …, d-1`) and `0` for the fictitious resource `d + 1` (Lean index
`Fin.last d`) (Sec. 5.1, p. 24). -/
def matchReward {d n : ℕ} (adj : Fin d → Fin n → Bool) (r : Fin d → Fin n → ℝ)
    (i : Fin (d + 1)) (j : Fin n) : ℝ :=
  if h : (i : ℕ) < d then r ⟨i, h⟩ j * adjR adj ⟨i, h⟩ j else 0

/-- Feasible set of the fluid matching LP `(P_t)` of Eq. (15), p. 24, for budgets `b ∈ ℝ^{d+1}`
(fictitious resource included) and right-hand side `y` (`y = E[Z(t)]`):
`Σ_j x_{ij} ≤ b_i` for all `i ∈ [d+1]`, `Σ_{i ∈ [d+1]} x_{ij} = y_j` for all `j`, `x ≥ 0`. -/
def matchFluidFeas {d n : ℕ} (b : Fin (d + 1) → ℝ) (y : Fin n → ℝ) :
    Set (Fin (d + 1) → Fin n → ℝ) :=
  {x | (∀ i, ∑ j, x i j ≤ b i) ∧ (∀ j, ∑ i, x i j = y j) ∧ ∀ i j, 0 ≤ x i j}

/-- Optimal solutions of `(P_t)` in Eq. (15): maximize `Σ_{i ∈ [d], j} x_{ij} r_{ij} a_{ij}`. -/
def matchFluidOpt {d n : ℕ} (adj : Fin d → Fin n → Bool) (r : Fin d → Fin n → ℝ)
    (b : Fin (d + 1) → ℝ) (y : Fin n → ℝ) : Set (Fin (d + 1) → Fin n → ℝ) :=
  {x | x ∈ matchFluidFeas b y ∧ ∀ x' ∈ matchFluidFeas b y,
    ∑ i, ∑ j, x' i j * matchReward adj r i j ≤ ∑ i, ∑ j, x i j * matchReward adj r i j}

/-- Online Matching (Sec. 2.1, p. 6; Sec. 5, pp. 23–24) with the fictitious resource `d + 1`
(Lean index `Fin.last d`): the state is the budget vector `b ∈ ℕ^{d+1}`; the action `i` matches the
arrival `j` to resource `i`, earning `r_{ij} a_{ij}` (`0` for the fictitious resource) and using one
unit of `i`; it is feasible iff `b_i ≥ 1`. -/
def matchingProblem {d n : ℕ} (adj : Fin d → Fin n → Bool) (r : Fin d → Fin n → ℝ) :
    OnlineProblem (Fin (d + 1) → ℕ) (Fin n) (Fin (d + 1)) where
  trans i b _ := Function.update b i (b i - 1)
  reward i _ j := matchReward adj r i j
  feasible b := {i | 1 ≤ b i}

/-- Initial state of the matching problem: the budgets `B ∈ ℕ^d` and `B_{d+1} = T` for the
fictitious resource (p. 24). -/
def matchInit {d : ℕ} (B : Fin d → ℕ) (T : ℕ) : Fin (d + 1) → ℕ :=
  fun i => if h : (i : ℕ) < d then B ⟨i, h⟩ else T

/-- `X` selects, at every time-to-go `t` and budget `b ∈ ℕ^{d+1}`, an optimal solution of `(P_t)` in
Eq. (15) whenever `(P_t)` is feasible. -/
def IsMatchingFluidSelection {d n T : ℕ} [NeZero n] (adj : Fin d → Fin n → Bool)
    (r : Fin d → Fin n → ℝ) (w : (Fin T → Fin n) → ℝ)
    (X : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → Fin n → ℝ) : Prop :=
  ∀ t b, (matchFluidFeas (fun i => (b i : ℝ)) (meanVec w t)).Nonempty →
    X t b ∈ matchFluidOpt adj r (fun i => (b i : ℝ)) (meanVec w t)

/-- `K t b j ∈ argmax{X^t_{ij} : i ∈ [d+1]}` (arbitrary tie breaking), Algorithm 3, line 3. -/
def IsArgmaxSelection {d n : ℕ} (X : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → Fin n → ℝ)
    (K : ℕ → (Fin (d + 1) → ℕ) → Fin n → Fin (d + 1)) : Prop :=
  ∀ t b j i, X t b i j ≤ X t b (K t b j) j

/-- The Fluid Bayes Selector for Online Matching (Algorithm 3, p. 25): on arrival `θ^t = j`, match
`j` to `K = K t B^t j`, a maximal entry of the column `X^t_{·j}`. If resource `K` has no unit left
(a case the paper's algorithm does not mention), the arrival is sent to the fictitious resource
(rejected). -/
def fluidBayesMatching {d n : ℕ} (K : ℕ → (Fin (d + 1) → ℕ) → Fin n → Fin (d + 1)) :
    Policy (Fin (d + 1) → ℕ) (Fin n) (Fin (d + 1)) :=
  fun t θ b => if 1 ≤ b (K t b (θ t)) then K t b (θ t) else Fin.last d

/-- Expected regret of Algorithm 3 with `T` periods to go and initial budgets `B` (plus `T` units of
the fictitious resource), under the arrival law `w`. -/
noncomputable def matchingExpectedRegret {d n T : ℕ} [NeZero n] (adj : Fin d → Fin n → Bool)
    (r : Fin d → Fin n → ℝ) (w : (Fin T → Fin n) → ℝ)
    (K : ℕ → (Fin (d + 1) → ℕ) → Fin n → Fin (d + 1)) (B : Fin d → ℕ) : ℝ :=
  expectL w (fun θ => (matchingProblem adj r).regret (fluidBayesMatching K) T (matchInit B T) θ)

/-- `r_max`: the largest reward of a single allocation, `max_{i,j} r_{ij} a_{ij}` (the maximal
bundle reward of the matching instance; `0` is attained by the fictitious resource). -/
noncomputable def matchRmax {d n : ℕ} [NeZero n] (adj : Fin d → Fin n → Bool)
    (r : Fin d → Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : Fin (d + 1) × Fin n => matchReward adj r p.1 p.2)

end BayesProphet.MultiSec.Supplement


