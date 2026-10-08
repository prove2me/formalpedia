-- Prove2me | Definitions.Def_MDPComplexity_PartiallyObserved_Model
-- name    : MDPComplexity_PartiallyObserved_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:36:02.018425+00:00
-- url     : https://prove2.me/theorems/cda3e19a-14e9-4330-82c9-2b3d8b34a820
-- title:
--   §4 (pp. 447–448): partially observed Markov decision process, observation-history policies, finite-horizon expected cost
-- statement:
--   This file sets up the **partially observed problem** of Papadimitriou and Tsitsiklis (§4, pp. 447–448).
--
--   A **partially observed (stationary) Markov decision process** consists of
--
--   1. a finite set $S$ of states and a partition $\Pi$ of $S$; we write $z(s) \in \Pi$ for the set of $\Pi$ that contains the state $s$ (the *observation* of $s$);
--   2. for each set $z \in \Pi$ a nonempty finite set $D_z$ of decisions, and for each decision $i \in D_z$ a cost $c(z, i) \in \mathbb{R}$;
--   3. for each state $s$ and each decision $i \in D_{z(s)}$ a probability distribution $p(s, \cdot, i)$ of the next state.
--
--   The controller never sees the state, only the sequence of sets of $\Pi$ visited so far. A **policy** $\pi$ is a mapping from finite sequences of observations $z_0, \dots, z_t$ to decisions $\pi(z_0, \dots, z_t) \in D_{z_t}$.
--
--   Fix an initial state $s_0$ and a horizon $T$. A trajectory is a sequence $x_0, \dots, x_T$ of states; under $\pi$ its probability is
--   $$
--   P_\pi(x) = [x_0 = s_0] \prod_{t=0}^{T-1} p\bigl(x_t, x_{t+1}, \pi(z(x_0), \dots, z(x_t))\bigr),
--   $$
--   and its cost is $\sum_{t=0}^{T} c\bigl(z(x_t), \pi(z(x_0), \dots, z(x_t))\bigr)$. The **expected cost** of $\pi$ is
--   $$
--   J_\pi(T) = \sum_{x \in S^{T+1}} P_\pi(x) \sum_{t=0}^{T} c\bigl(z(x_t), \pi(z(x_0), \dots, z(x_t))\bigr),
--   $$
--   and the **optimal expected cost** is $J^*(T) = \inf_\pi J_\pi(T)$, the infimum over all observation-history policies.
--
--   These objects carry the hardness result of the paper (Theorem 6): deciding whether a cost can be achieved in such a process is PSPACE-hard.
--
--   **Formalization Note.** The partition is encoded by an observation map `obs : S → Z`: the sets of $\Pi$ are the nonempty fibres of `obs`. Next-state distributions are Mathlib `PMF`s, so every row is a probability vector by construction; the paper's $p(s, s', i)$ is `(p s i s').toReal`. The paper says "a set $D_z$ of decisions"; we require it nonempty and finite (a policy must choose a decision). A policy is `π hist z` with `hist` the earlier observations, oldest first, and `z` the current one; this is the paper's mapping on $z_1, \dots, z_t$ with $z_t$ = `z`. The expectation is written as a sum over trajectories, not as a dynamic-programming recursion. The cost sums over times $0, \dots, T$, as printed on p. 444. The infimum is over all policies; it is a genuine infimum since there are finitely many trajectories with bounded costs, so the family is bounded below.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), pp. 444 and 447–448, §2 Markov Decision Processes and §4 The partially observed problem

import Mathlib

namespace MDPComplexity.PartiallyObserved

open Finset

/-- §4 (pp. 447–448): a finite, stationary, partially observed Markov decision process.
The partition Π of the state set `S` is given by the observation map `obs : S → Z`: the set of Π
containing `s` is `obs s` (so the sets of Π are the nonempty fibres of `obs`). Each set `z` has a
nonempty finite set of decisions `D z`; decision `i ∈ D z` has cost `c z i` and, from a current
state `s ∈ z`, the next-state distribution `p s i` (a probability mass function on `S`, the paper's
`p(s, s′, i)`). -/
structure POMDP (S Z : Type) where
  obs : S → Z
  D : Z → Type
  [instFintype : ∀ z, Fintype (D z)]
  [instNonempty : ∀ z, Nonempty (D z)]
  c : (z : Z) → D z → ℝ
  p : (s : S) → D (obs s) → PMF S

attribute [instance] POMDP.instFintype POMDP.instNonempty

variable {S Z : Type}

/-- "A policy is now a mapping from sequences of observations z_1, ..., z_t to decisions in
D_{z_t}" (p. 448). `π hist z` is the decision taken when the earlier observations are `hist`
(oldest first) and the current observation is `z`. -/
def POMDP.Policy (M : POMDP S Z) : Type := List Z → (z : Z) → M.D z

/-- The observations `obs (x 0), …, obs (x (t − 1))` made strictly before time `t` along a
trajectory `x 0, …, x T`, oldest first. -/
def POMDP.obsHist (M : POMDP S Z) {T : ℕ} (x : Fin (T + 1) → S) (t : Fin (T + 1)) : List Z :=
  List.ofFn (fun k : Fin t.val => M.obs (x (Fin.castLE t.isLt.le k)))

/-- The decision `π(z_0, …, z_t)` taken at time `t` along the trajectory `x`. -/
def POMDP.dec (M : POMDP S Z) (π : M.Policy) {T : ℕ} (x : Fin (T + 1) → S)
    (t : Fin (T + 1)) : M.D (M.obs (x t)) :=
  π (M.obsHist x t) (M.obs (x t))

/-- Probability, under policy `π` from the initial state `s₀`, of the trajectory
`x 0, …, x T`: `[x 0 = s₀] · ∏_{t<T} p(x t, x (t+1), π(z_0, …, z_t))`. -/
noncomputable def POMDP.trajProb (M : POMDP S Z) [DecidableEq S] (s₀ : S) (π : M.Policy)
    (T : ℕ) (x : Fin (T + 1) → S) : ℝ :=
  (if x 0 = s₀ then 1 else 0) *
    ∏ t : Fin T, ((M.p (x t.castSucc) (M.dec π x t.castSucc)) (x t.succ)).toReal

/-- The cost `Σ_{t=0}^{T} c(z_t, π(z_0, …, z_t))` of the trajectory `x 0, …, x T`. -/
noncomputable def POMDP.trajCost (M : POMDP S Z) (π : M.Policy) (T : ℕ)
    (x : Fin (T + 1) → S) : ℝ :=
  ∑ t : Fin (T + 1), M.c (M.obs (x t)) (M.dec π x t)

/-- The expected finite-horizon cost of policy `π` from `s₀` with horizon `T`
(p. 444 and p. 448), written as a sum over all trajectories `x 0, …, x T`. -/
noncomputable def POMDP.expCost (M : POMDP S Z) [Fintype S] [DecidableEq S] (s₀ : S)
    (π : M.Policy) (T : ℕ) : ℝ :=
  ∑ x : Fin (T + 1) → S, M.trajProb s₀ π T x * M.trajCost π T x

/-- The optimal expected cost: the infimum of `expCost` over all observation-history
policies. -/
noncomputable def POMDP.optCost (M : POMDP S Z) [Fintype S] [DecidableEq S] (s₀ : S)
    (T : ℕ) : ℝ :=
  ⨅ π : M.Policy, M.expCost s₀ π T

end MDPComplexity.PartiallyObserved


