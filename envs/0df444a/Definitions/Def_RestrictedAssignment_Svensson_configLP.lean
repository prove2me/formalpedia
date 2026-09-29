-- Prove2me | Definitions.Def_RestrictedAssignment_Svensson_configLP
-- name    : RestrictedAssignment_Svensson_configLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:25:59.365984+00:00
-- url     : https://prove2.me/theorems/274dd1b3-37f2-40e8-826e-2fd31e45018b
-- title:
--   Configurations and the configuration LP [C-LP] of restricted assignment
-- statement:
--   In the **restricted assignment problem** we are given a finite set $J$ of jobs, a finite set $M$ of machines, a size $p_j \ge 0$ for each job $j$, and for each job a set $\Gamma(j) \subseteq M$ of machines on which it may be processed. A **schedule** is a map $\sigma : J \to M$ with $\sigma(j) \in \Gamma(j)$ for every job; the **load** of machine $i$ is $p(\sigma^{-1}(i)) = \sum_{j : \sigma(j) = i} p_j$, where $p(J') = \sum_{j \in J'} p_j$, and the makespan of $\sigma$ is the largest load.
--
--   For a target makespan $T$ and a machine $i$, a **configuration** for $i$ is a set of jobs $C \subseteq J$ that fits on $i$ within $T$:
--   $$
--   \mathcal C(i,T) = \{\, C \subseteq J \;:\; i \in \Gamma(j) \text{ for all } j \in C,\ \ p(C) \le T \,\}.
--   $$
--   The **configuration LP** [C-LP] has a variable $x_{i,C}$ for each machine $i$ and each $C \in \mathcal C(i,T)$, and is **feasible** if there are values with
--   $$
--   \sum_{C \in \mathcal C(i,T)} x_{i,C} \le 1 \ \ (i \in M), \qquad \sum_{i \in M}\ \sum_{C \in \mathcal C(i,T),\, C \ni j} x_{i,C} \ge 1 \ \ (j \in J), \qquad x \ge 0 .
--   $$
--   Its **dual** has variables $y_i$ ($i \in M$) and $z_j$ ($j \in J$); a pair $(y,z)$ is dual feasible if $y, z \ge 0$ and $y_i \ge \sum_{j \in C} z_j$ for every machine $i$ and every $C \in \mathcal C(i,T)$.
--
--   These are the objects in terms of which the integrality gap of [C-LP] is stated. The least $T$ for which [C-LP] is feasible is the LP lower bound $\mathrm{OPT}_{LP}$ on the optimal makespan.
--
--   **Formalization Note** `configs Γ p T i` is $\mathcal C(i,T)$ as a finite set of finite sets of jobs; `CLPFeasible Γ p T` is feasibility of [C-LP]; `CLPDualFeasible Γ p T y z` is dual feasibility; `schedLoad p σ i` is the load of machine $i$ under a total schedule $\sigma : J \to M$. The LP variable is a function `x : M → Finset J → ℝ`; its values at sets that are not configurations of $i$ appear in no constraint. The constraint $\sigma(j) \in \Gamma(j)$ on schedules is stated where schedules are used.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 1 (model), p. 3, Sect. 2, [C-LP], p. 4, Dual of [C-LP]

import Mathlib

namespace RestrictedAssignment.Svensson

open Finset

variable {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]

/-- Svensson, arXiv:1011.1168v2, p. 3, Sect. 2: `C(i, T)`, the configurations for machine `i`
with respect to the target makespan `T`: the sets of jobs `C ⊆ J` with `C ⊆ {j : i ∈ Γ(j)}` and
`p(C) = ∑_{j ∈ C} p_j ≤ T`. -/
noncomputable def configs (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (i : M) : Finset (Finset J) :=
  (Finset.univ : Finset (Finset J)).filter (fun C => (∀ j ∈ C, i ∈ Γ j) ∧ ∑ j ∈ C, p j ≤ T)

/-- Svensson, arXiv:1011.1168v2, p. 3, [C-LP]: the configuration LP for target makespan `T` is
feasible, i.e. there are `x_{i,C} ≥ 0` with `∑_{C ∈ C(i,T)} x_{i,C} ≤ 1` for every machine `i`
and `∑_i ∑_{C ∈ C(i,T), C ∋ j} x_{i,C} ≥ 1` for every job `j`. (Values of `x` at sets that are
not configurations of `i` occur in no constraint.) -/
def CLPFeasible (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) : Prop :=
  ∃ x : M → Finset J → ℝ,
    (∀ i C, 0 ≤ x i C) ∧
    (∀ i, ∑ C ∈ configs Γ p T i, x i C ≤ 1) ∧
    (∀ j, 1 ≤ ∑ i, ∑ C ∈ (configs Γ p T i).filter (fun C => j ∈ C), x i C)

/-- Svensson, arXiv:1011.1168v2, p. 4, Dual of [C-LP]: `(y, z)` is a feasible solution of the
dual, i.e. `y, z ≥ 0` and `y_i ≥ ∑_{j ∈ C} z_j` for every machine `i` and every `C ∈ C(i, T)`. -/
def CLPDualFeasible (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (y : M → ℝ) (z : J → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ z j) ∧ ∀ i, ∀ C ∈ configs Γ p T i, ∑ j ∈ C, z j ≤ y i

/-- Svensson, arXiv:1011.1168v2, p. 1: the load `∑_{j ∈ σ⁻¹(i)} p_j` of machine `i` under a
schedule `σ : J → M`; the makespan of `σ` is the maximum load. -/
def schedLoad (p : J → ℝ) (σ : J → M) (i : M) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = i), p j

end RestrictedAssignment.Svensson


