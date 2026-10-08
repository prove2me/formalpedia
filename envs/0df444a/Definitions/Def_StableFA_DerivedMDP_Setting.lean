-- Prove2me | Definitions.Def_StableFA_DerivedMDP_Setting
-- name    : StableFA_DerivedMDP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:37.191425+00:00
-- url     : https://prove2.me/theorems/72d8865f-6c72-4d6e-83e0-1b335c6ee502
-- title:
--   §§2–4, pp. 3–10 — averagers with a goal weight, the derived MDP M′, proper policies, the layer partition S_k, self-weighted averagers
-- statement:
--   This file sets up the objects of §4 (*Nondiscounted processes*) of Gordon's report. The Markov decision process is a finite stochastic shortest path model $M$: non-goal states $1,\dots,n$, finite nonempty action sets $U(x)$, expected one-step costs $c_{xa}$, and transition probabilities $p_{axy}$ between non-goal states with $\sum_y p_{axy}\le 1$; the missing mass $1-\sum_y p_{axy}$ is the probability of moving to the cost-free absorbing goal state, which the paper calls state $1$. Value functions are vectors $V\in\mathbb R^n$ on the non-goal states; the goal's value is $V(1)=0$ (p. 4: "we define the backup operator to set $V(g)\leftarrow 0$ as a special case").
--
--   1. **Averager** (p. 7). An averager $A$ consists of constants $k_y$, nonnegative weights $\beta_y$ and nonnegative weights $\beta_{yz}$, for every non-goal state $y$ and every state $z$ (the goal included: $\beta_{y1}$ is the weight on the goal), with
--   $$\beta_y+\sum_z \beta_{yz}=1 .$$
--   Its mapping $M_A$ sends a value function $V$ to $M_A(V)(y)=\beta_y k_y+\sum_z\beta_{yz}V(z)$; the goal term $\beta_{y1}V(1)$ vanishes. On the goal itself the averager keeps $V(1)=0$ ($\beta_1=1$, $k_1=0$).
--
--   2. **Compatible operators** (p. 5). Two operators $M_F$ and $T$ on value functions are compatible if for every initial guess $x_0$ the iterates $(M_F\circ T)^k(x_0)$, $k=0,1,2,\dots$, converge to some point.
--
--   3. **The derived MDP** (proof of Theorem 4.1, p. 9). For a discount factor $\gamma$, $M'$ has the same states and actions as $M$, and
--   $$p'_{axz}=\sum_y p_{axy}\beta_{yz}\quad(z\neq 1),\qquad c'_{xa}=c_{xa}+\gamma\sum_{y'}p_{axy'}\beta_{y'}k_{y'} ;$$
--   the remaining probability $1-\sum_{z\ne 1}p'_{axz}$, which equals $p_{ax1}+\sum_y p_{axy}(\beta_{y1}+\beta_y)$, goes to the goal.
--
--   4. **Proper policies** (p. 3). A policy is a function $\mu$ from states to admissible actions; it is *proper* if, from every starting state, the probability of still being outside the goal after $t$ steps tends to $0$ as $t\to\infty$, i.e. $P(x_t=1)\to 1$.
--
--   5. **Partition by distance from the goal** (p. 10). $S_1=\{1\}$, $U_k=\bigcup_{j<k}S_j$, and for $k\ge 2$
--   $$S_k=\Bigl\{x \;\Bigm|\; x\notin U_k \ \wedge\ \min_{a}\max_{y\in U_k}P(\delta(x,a)=y)>0\Bigr\},$$
--   i.e. $x$ is not in an earlier layer and *every* admissible action at $x$ reaches some state of $U_k$ with positive probability. The index $k=0$ carries the empty set.
--
--   6. **Self-weighted averagers** (p. 10). $A$ is self-weighted for $M$ if for every state $y$ either $\beta_y>0$ or $\beta_{yx}>0$ for some state $x$ with $k(x)\le k(y)$, where $k(x)$ is the index of the layer containing $x$.
--
--   These are the objects in terms of which Gordon shows that approximate value iteration through an averager is exact value iteration on a derived MDP, and that the derived MDP of a self-weighted averager reaches the goal with probability one.
--
--   **Formalization Note** The goal state 1 is the implicit termination state of the published model `BertsekasSSPModel`; where the partition and the averager's goal weight need to name it, it is `none` in `Option (Fin n)`. This realises the page's two "without loss of generality" steps (state 1 cost-free and absorbing; $\beta_1=1$, $k_1=0$) by construction. The averager acts on whole value functions over the state set; an approximator that ignores $V(x)$ for $x$ outside a sample $X_0$ is the special case $\beta_{yx}=0$. The partition is built through the cumulative unions `below M k` $=U_k$; the lemmas `below_eq_iUnion` and `mem_layer_iff` give the defining property above. `SelfWeighted` states $k(x)\le k(y)$ through membership in layers, which agrees with the page whenever $k$ is defined (the partition is exhaustive when all policies are proper); only non-goal $y$ are quantified, since for the goal $\beta_1=1>0$.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 3 (absorbing goal, proper strategies, policies), p. 4 (backup sets V(g) ← 0), p. 5 (compatible), p. 7 (averager), p. 9 (derived MDP M′ in the proof of Theorem 4.1), p. 10 (partition S_k, self-weighted)

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting

namespace StableFA.DerivedMDP

open Filter Topology

/-- An averager (Gordon 1995, p. 7) for a finite MDP whose non-goal states are `Fin n` and
whose goal state ("state 1") is represented by `none : Option (Fin n)`. For each non-goal
state `y` there is a constant `k y`, a nonnegative weight `βc y` on that constant (the paper's
`β_y`) and nonnegative weights `β y z` (the paper's `β_yz`) on the target values at every
state `z`, the goal included (`β y none` is the paper's `β_y1`), with
`βc y + ∑ z, β y z = 1`. The goal's own row is `β_1 = 1`, `k_1 = 0` (the averager keeps the
goal's value `V(1) = 0`); it is implicit. -/
structure Averager (n : ℕ) where
  /-- the predetermined constants `k_y` -/
  k : Fin n → ℝ
  /-- the weight `β_y` on the constant `k_y` -/
  βc : Fin n → ℝ
  /-- the weight `β_yz` of the target value at state `z` (`none` = the goal state 1) -/
  β : Fin n → Option (Fin n) → ℝ
  βc_nonneg : ∀ y, 0 ≤ βc y
  β_nonneg : ∀ y z, 0 ≤ β y z
  sum_eq_one : ∀ y, βc y + ∑ z : Option (Fin n), β y z = 1

/-- The mapping `M_A` of the averager `A` (pp. 5, 7, 9): the fitted value at a non-goal state
`y` is `β_y k_y + ∑_z β_yz V(z)`; the goal's value `V(1)` is `0`, so its term vanishes. -/
def Averager.apply {n : ℕ} (A : Averager n) (V : Fin n → ℝ) : Fin n → ℝ :=
  fun y => A.βc y * A.k y + ∑ z : Fin n, A.β y (some z) * V z

variable {n : ℕ} {C : Type} [Fintype C]

/-- The derived MDP `M′` of Theorem 4.1 (p. 9), for discount factor `γ`: same states and
actions as `M`, transition probabilities `p′_xuz = ∑_y p_xuy β_yz` to non-goal states `z`
(the remaining mass `1 - ∑_z p′_xuz = p_xu1 + ∑_y p_xuy (β_y1 + β_y)` goes to the goal), and
expected costs `c′_xu = c_xu + γ ∑_y p_xuy β_y k_y`. -/
def derivedModel (M : BertsekasSSPModel n C) (A : Averager n) (γ : ℝ) :
    BertsekasSSPModel n C where
  U := M.U
  hU := M.hU
  p x u z := ∑ y, M.p x u y * A.β y (some z)
  g x u := M.g x u + γ * ∑ y, M.p x u y * A.βc y * A.k y
  hp_nonneg x u z :=
    Finset.sum_nonneg fun y _ => mul_nonneg (M.hp_nonneg x u y) (A.β_nonneg y (some z))
  hp_sum x u hu := by
    rw [Finset.sum_comm]
    refine le_trans ?_ (M.hp_sum x u hu)
    refine Finset.sum_le_sum fun y _ => ?_
    rw [← Finset.mul_sum]
    have h := A.sum_eq_one y
    rw [Fintype.sum_option] at h
    have h1 : ∑ z : Fin n, A.β y (some z) ≤ 1 := by
      linarith [A.βc_nonneg y, A.β_nonneg y none]
    simpa using mul_le_mul_of_nonneg_left h1 (M.hp_nonneg x u y)

/-- A stationary policy `μ` (a function from states to actions, p. 3) is proper if, from every
starting state, the probability of not yet having reached the goal after `t` steps tends to
`0`, i.e. `P(x_t = 1) → 1` as `t → ∞`. -/
def IsProper (M : BertsekasSSPModel n C) (μ : Fin n → C) : Prop :=
  ∀ i, Tendsto (fun t => BertsekasSSPSurvival M (fun _ => μ) t i) atTop (𝓝 0)

/-- The one-step law of `M` on the full state space `Option (Fin n)` (`none` = the goal):
from state `i` under action `u`, the goal is reached with probability `1 - ∑_j p_iuj` and the
non-goal state `j` with probability `p_iuj`. -/
def stepProb (M : BertsekasSSPModel n C) (i : Fin n) (u : C) : Option (Fin n) → ℝ
  | none => 1 - ∑ j, M.p i u j
  | some j => M.p i u j

/-- The layer built on a set `U` of states (p. 10): the states `x ∉ U` (necessarily non-goal)
such that every admissible action at `x` moves to some state of `U` with positive probability,
`min_{a} max_{y ∈ U} P(δ(x, a) = y) > 0`. -/
def nextLayer (M : BertsekasSSPModel n C) (U : Set (Option (Fin n))) :
    Set (Option (Fin n)) :=
  {x | x ∉ U ∧ ∃ i, x = some i ∧ ∀ u ∈ M.U i, ∃ y ∈ U, 0 < stepProb M i u y}

/-- `below M k` is the paper's `U_k = ⋃_{j<k} S_j` (p. 10), with `S_0 = ∅` and `S_1 = {1}`:
`U_0 = U_1 = ∅`, `U_2 = {1}`, and `U_{k+1} = U_k ∪ S_k` for `k ≥ 2`. -/
def below (M : BertsekasSSPModel n C) : ℕ → Set (Option (Fin n))
  | 0 => ∅
  | 1 => ∅
  | 2 => {none}
  | k + 3 => below M (k + 2) ∪ nextLayer M (below M (k + 2))

/-- The partition of the state space by distance from the goal (p. 10): `S_0 = ∅`,
`S_1 = {1}`, and for `k ≥ 2`, `S_k = {x | x ∉ U_k ∧ min_a max_{y ∈ U_k} P(δ(x, a) = y) > 0}`. -/
def layer (M : BertsekasSSPModel n C) : ℕ → Set (Option (Fin n))
  | 0 => ∅
  | 1 => {none}
  | k + 2 => nextLayer M (below M (k + 2))

/-- `U_k` is the union of the earlier layers. -/
theorem below_eq_iUnion (M : BertsekasSSPModel n C) (k : ℕ) :
    below M k = ⋃ j < k, layer M j := by
  induction k with
  | zero => simp [below]
  | succ k ih =>
    rcases k with _ | _ | k
    · ext x; simp [below, layer]
    · ext x
      simp only [below, layer, Set.mem_singleton_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro rfl; exact ⟨1, by omega, rfl⟩
      · rintro ⟨j, hj, hx⟩
        rcases j with _ | _ | j
        · simp at hx
        · exact hx
        · omega
    · ext x
      have e : below M (k + 3) = below M (k + 2) ∪ layer M (k + 2) := rfl
      rw [e, ih]
      simp only [Set.mem_union, Set.mem_iUnion, exists_prop]
      constructor
      · rintro (⟨j, hj, hx⟩ | hx)
        · exact ⟨j, by omega, hx⟩
        · exact ⟨k + 2, by omega, hx⟩
      · rintro ⟨j, hj, hx⟩
        by_cases hjk : j < k + 2
        · exact Or.inl ⟨j, hjk, hx⟩
        · obtain rfl : j = k + 2 := by omega
          exact Or.inr hx

/-- The defining property of the layers `S_k`, `k ≥ 2` (p. 10). -/
theorem mem_layer_iff (M : BertsekasSSPModel n C) (k : ℕ) (x : Option (Fin n)) :
    x ∈ layer M (k + 2) ↔
      x ∉ (⋃ j < k + 2, layer M j) ∧
        ∃ i, x = some i ∧ ∀ u ∈ M.U i, ∃ y ∈ (⋃ j < k + 2, layer M j),
          0 < stepProb M i u y := by
  rw [← below_eq_iUnion]; rfl

/-- The averager `A` is self-weighted for `M` (p. 10): for every non-goal state `y`, either
`β_y > 0`, or `β_yx > 0` for some state `x` (the goal included) lying in a layer no later than
that of `y`, i.e. `k(x) ≤ k(y)`. (For the goal `y = 1` the condition holds since `β_1 = 1`.) -/
def SelfWeighted (M : BertsekasSSPModel n C) (A : Averager n) : Prop :=
  ∀ y : Fin n, 0 < A.βc y ∨
    ∃ x : Option (Fin n), 0 < A.β y x ∧
      ∃ kx ky : ℕ, x ∈ layer M kx ∧ some y ∈ layer M ky ∧ kx ≤ ky

end StableFA.DerivedMDP


