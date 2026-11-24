-- Prove2me | Definitions.Def_BayesProphet_MultiSec_Supplement_Allocation
-- name    : BayesProphet_MultiSec_Supplement_Allocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:11:40.702427+00:00
-- url     : https://prove2.me/theorems/5beca43a-65ed-4a8e-993e-b244c40b65bb
-- title:
--   Online Allocation with multiset bundles, the LP of Eq. (16) and the Fluid Bayes Selector (Algorithm 4)
-- statement:
--   This file defines the general Online Allocation problem and Algorithm 4.
--
--   **Model** (Sec. 2.1, Sec. 6). There are $d$ resources and $n$ types. Type $j$ has a finite collection $S_j$ of $m_j$ distinct bundles; a bundle $s$ is a multiset of resources, with $a_{is}\in\mathbb N$ copies of resource $i$, and assigning $s$ to a type-$j$ agent earns $r_{sj}$ and consumes $a_{is}$ units of each $i$. Rewards need not be additive. A fictitious resource $d+1$ with initial capacity $T$ and a fictitious bundle $\{d+1\}$ of reward $0$, available to every type, represent rejection. The state is $b\in\mathbb N^{d+1}$, the initial state is $(B,T)$, and assigning a bundle is feasible iff its consumption is at most $b$. $r_{\max}$ is the largest bundle reward (the fictitious bundle included).
--
--   **Fluid LP** (Eq. (16)). For $b\in\mathbb R^{d+1}$,
--   $$(P_t):\quad\max\sum_{j,s}x_{sj}r_{sj}\ \text{ s.t. }\ \sum_{j,s}a_{is}x_{sj}\le b_i\ (i\in[d+1]),\ \ \sum_{s}x_{sj}=\mathbb E[Z_j(t)]\ (j\in[n]),\ \ x\ge0,$$
--   where $s$ ranges over $S_j$ and the fictitious bundle.
--
--   **Fluid Bayes Selector** (Algorithm 4). With $t$ periods to go and budget $B^t$, let $X^t$ be an optimal solution of $(P_t)$; on arrival $\theta^t=j$ let $K\in\arg\max\{X^t_{sj}\}$ over the bundles of $j$ and the fictitious bundle (ties arbitrary). If $K$ cannot be assigned, reject (assign the fictitious bundle); otherwise assign $K$.
--
--   **Formalization Note** The real bundles of type $j$ are indexed by `Fin (m j)` and `none` is the fictitious bundle; resource $d+1$ is `Fin.last d`. An action $\langle k,s\rangle$ assigns $s$ if the arrival is of type $k$ and does nothing otherwise (Offline's value is unchanged by these extra no-op actions). The selection $X$ is required to be optimal whenever $(P_t)$ is feasible.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 5 (Sec. 2.1), p. 26 (Eq. (16), Algorithm 4)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary
import Definitions.Def_BayesProphet_MultiSec_Supplement_Arrivals

namespace BayesProphet.MultiSec.Supplement

open BayesProphet.MultiSec

/-- Resource consumption `a_{is}` of a bundle of type `j` (Sec. 2.1, p. 5; Sec. 6, p. 26), over the
`d + 1` resources including the fictitious resource `d + 1` (Lean index `Fin.last d`). The real
bundles of type `j` are indexed by `Fin (m j)`; `bund j s i ∈ ℕ` is the multiplicity of resource `i`
in the multiset bundle `s` (real bundles never use the fictitious resource). The option `none` is the
fictitious bundle `{d + 1}`, which uses one unit of resource `d + 1` and nothing else. -/
def allocCons {d n : ℕ} {m : Fin n → ℕ} (bund : (j : Fin n) → Fin (m j) → Fin d → ℕ)
    (j : Fin n) : Option (Fin (m j)) → Fin (d + 1) → ℕ
  | none => fun i => if (i : ℕ) = d then 1 else 0
  | some s => fun i => if h : (i : ℕ) < d then bund j s ⟨i, h⟩ else 0

/-- Reward `r_{sj}` of giving bundle `s` to type `j`; the fictitious bundle has reward `0` (p. 26). -/
def allocReward {n : ℕ} {m : Fin n → ℕ} (rew : (j : Fin n) → Fin (m j) → ℝ) (j : Fin n) :
    Option (Fin (m j)) → ℝ
  | none => 0
  | some s => rew j s

/-- Feasible set of the fluid allocation LP `(P_t)` of Eq. (16), p. 26, with budgets `b ∈ ℝ^{d+1}`
and right-hand side `y` (`y = E[Z(t)]`): `Σ_{j, s ∈ S_j} a_{is} x_{sj} ≤ b_i` for all `i ∈ [d+1]`,
`Σ_{s ∈ S_j} x_{sj} = y_j` for all `j` (`S_j` including the fictitious bundle), `x ≥ 0`. -/
def allocFluidFeas {d n : ℕ} {m : Fin n → ℕ} (bund : (j : Fin n) → Fin (m j) → Fin d → ℕ)
    (b : Fin (d + 1) → ℝ) (y : Fin n → ℝ) : Set ((j : Fin n) → Option (Fin (m j)) → ℝ) :=
  {x | (∀ i, ∑ j, ∑ s, (allocCons bund j s i : ℝ) * x j s ≤ b i) ∧
    (∀ j, ∑ s, x j s = y j) ∧ ∀ j s, 0 ≤ x j s}

/-- Optimal solutions of `(P_t)` in Eq. (16): maximize `Σ_{j, s} x_{sj} r_{sj}`. -/
def allocFluidOpt {d n : ℕ} {m : Fin n → ℕ} (bund : (j : Fin n) → Fin (m j) → Fin d → ℕ)
    (rew : (j : Fin n) → Fin (m j) → ℝ) (b : Fin (d + 1) → ℝ) (y : Fin n → ℝ) :
    Set ((j : Fin n) → Option (Fin (m j)) → ℝ) :=
  {x | x ∈ allocFluidFeas bund b y ∧ ∀ x' ∈ allocFluidFeas bund b y,
    ∑ j, ∑ s, x' j s * allocReward rew j s ≤ ∑ j, ∑ s, x j s * allocReward rew j s}

/-- Online Allocation (Sec. 2.1, p. 5; Sec. 6, p. 26) as an online decision problem: the state is
the budget vector `b ∈ ℕ^{d+1}` (fictitious resource included); the action `⟨k, s⟩` assigns bundle
`s` (possibly the fictitious one) to the arrival if it is of type `k`, earning `r_{sk}` and consuming
`a_{·s}`, and does nothing otherwise. It is feasible iff `a_{·s} ≤ b`. -/
def allocationProblem {d n : ℕ} {m : Fin n → ℕ} (bund : (j : Fin n) → Fin (m j) → Fin d → ℕ)
    (rew : (j : Fin n) → Fin (m j) → ℝ) :
    OnlineProblem (Fin (d + 1) → ℕ) (Fin n) ((j : Fin n) × Option (Fin (m j))) where
  trans a b j := if a.1 = j then b - allocCons bund a.1 a.2 else b
  reward a _ j := if a.1 = j then allocReward rew a.1 a.2 else 0
  feasible b := {a | allocCons bund a.1 a.2 ≤ b}

/-- `X` selects, at every time-to-go `t` and budget `b ∈ ℕ^{d+1}`, an optimal solution of `(P_t)`
in Eq. (16) whenever `(P_t)` is feasible. -/
def IsAllocFluidSelection {d n T : ℕ} [NeZero n] {m : Fin n → ℕ}
    (bund : (j : Fin n) → Fin (m j) → Fin d → ℕ) (rew : (j : Fin n) → Fin (m j) → ℝ)
    (w : (Fin T → Fin n) → ℝ)
    (X : ℕ → (Fin (d + 1) → ℕ) → (j : Fin n) → Option (Fin (m j)) → ℝ) : Prop :=
  ∀ t b, (allocFluidFeas bund (fun i => (b i : ℝ)) (meanVec w t)).Nonempty →
    X t b ∈ allocFluidOpt bund rew (fun i => (b i : ℝ)) (meanVec w t)

/-- `K t b j ∈ argmax{X^t_{sj} : s ∈ S_j}` (fictitious bundle included, arbitrary tie breaking),
Algorithm 4, line 3. -/
def IsAllocArgmaxSelection {d n : ℕ} {m : Fin n → ℕ}
    (X : ℕ → (Fin (d + 1) → ℕ) → (j : Fin n) → Option (Fin (m j)) → ℝ)
    (K : ℕ → (Fin (d + 1) → ℕ) → (j : Fin n) → Option (Fin (m j))) : Prop :=
  ∀ t b j s, X t b j s ≤ X t b j (K t b j)

/-- The Fluid Bayes Selector for Online Allocation (Algorithm 4, p. 26): on arrival `θ^t = j`, let
`K = K t B^t j`; if bundle `K` can be assigned (`a_{·K} ≤ B^t`) assign it, otherwise reject, i.e.
assign the fictitious bundle. -/
noncomputable def fluidBayesAllocation {d n : ℕ} {m : Fin n → ℕ} (bund : (j : Fin n) → Fin (m j) → Fin d → ℕ)
    (K : ℕ → (Fin (d + 1) → ℕ) → (j : Fin n) → Option (Fin (m j))) :
    Policy (Fin (d + 1) → ℕ) (Fin n) ((j : Fin n) × Option (Fin (m j))) :=
  fun t θ b => by
    classical exact
      if allocCons bund (θ t) (K t b (θ t)) ≤ b then ⟨θ t, K t b (θ t)⟩ else ⟨θ t, none⟩

/-- Initial state: the budgets `B ∈ ℕ^d` and `B_{d+1} = T` for the fictitious resource (p. 26). -/
def allocInit {d : ℕ} (B : Fin d → ℕ) (T : ℕ) : Fin (d + 1) → ℕ :=
  fun i => if h : (i : ℕ) < d then B ⟨i, h⟩ else T

/-- Expected regret of Algorithm 4 with `T` periods to go and initial budgets `B` (plus `T` units of
the fictitious resource), under the arrival law `w`. -/
noncomputable def allocationExpectedRegret {d n T : ℕ} [NeZero n] {m : Fin n → ℕ}
    (bund : (j : Fin n) → Fin (m j) → Fin d → ℕ) (rew : (j : Fin n) → Fin (m j) → ℝ)
    (w : (Fin T → Fin n) → ℝ)
    (K : ℕ → (Fin (d + 1) → ℕ) → (j : Fin n) → Option (Fin (m j))) (B : Fin d → ℕ) : ℝ :=
  expectL w (fun θ =>
    (allocationProblem bund rew).regret (fluidBayesAllocation bund K) T (allocInit B T) θ)

/-- `r_max = max_{j, s ∈ S_j} r_{sj}`, the maximal bundle reward (the fictitious bundle, of reward
`0`, included). -/
noncomputable def allocRmax {n : ℕ} [NeZero n] {m : Fin n → ℕ}
    (rew : (j : Fin n) → Fin (m j) → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, none⟩, Finset.mem_univ _⟩
    (fun a : (j : Fin n) × Option (Fin (m j)) => allocReward rew a.1 a.2)

end BayesProphet.MultiSec.Supplement


