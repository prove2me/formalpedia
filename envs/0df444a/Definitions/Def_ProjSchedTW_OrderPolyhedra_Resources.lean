-- Prove2me | Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
-- name    : ProjSchedTW_OrderPolyhedra_Resources
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T15:04:47.711385+00:00
-- url     : https://prove2.me/theorems/ba03cc69-da87-40f3-945d-b34834a525ca
-- title:
--   §2.1 and Definition 2.3.9 — active sets, resource-feasible schedules and minimal forbidden sets
-- statement:
--   Resource constraints and forbidden sets for a project with renewable resources (§2.1 and Definition 2.3.9 of Neumann, Schwindt & Zimmermann).
--
--   For a schedule $S$ and a time $t$, the **active set** is
--   $$\mathcal A(S,t) = \{ i \in V \mid S_i \le t < S_i + p_i \}, \tag{2.1.1}$$
--   and $r_k(S,t) = \sum_{i \in \mathcal A(S,t)} r_{ik}$ is the amount of resource $k$ in use at time $t$ (Eq. (2.1.2)). A schedule is **resource-feasible** if
--   $$r_k(S,t) \le R_k \qquad \text{for all } k \in \mathcal R \text{ and all } t \ge 0,$$
--   and **feasible** if it is time-feasible and resource-feasible (Definition 2.1.1); the feasible region is $\mathcal S = \mathcal S_T \cap \mathcal S_R$.
--
--   A set $F \subseteq V$ is **forbidden** if $\sum_{i \in F} r_{ik} > R_k$ for some $k \in \mathcal R$ (Eq. (2.3.1)), and a **minimal forbidden set** is a forbidden set no proper subset of which is forbidden. A set that is not forbidden is **feasible**.
--
--   Minimal forbidden sets are the combinatorial objects through which the resource constraints enter the characterization of feasible strict orders.
--
--   **Formalization Note** The book writes the resource constraints (2.1.4) for $0 \le t \le \bar d$. In Chapter 2 schedules are not bounded by $\bar d$, and the book's proofs and Remark 2.3.11 use every $t \ge 0$; this file uses every $t \ge 0$. Minimality is Mathlib's `Minimal` with respect to inclusion of finite sets.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 25, Eqs. (2.1.1), (2.1.2), (2.1.4), Definition 2.1.1; p. 34, Definition 2.3.9, Eq. (2.3.1)

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project

namespace ProjSchedTW.OrderPolyhedra

open Classical in
/-- The active set `A(S, t) = {i ∈ V | S_i ≤ t < S_i + p_i}` of activities in progress at time
`t` under schedule `S` (Eq. (2.1.1), p. 25). -/
noncomputable def Project.activeSet {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (t : ℝ) : Finset (Fin (n + 2)) :=
  Finset.univ.filter (fun i => S i ≤ t ∧ t < S i + (P.p i : ℝ))

/-- The amount `r_k(S, t) = ∑_{i ∈ A(S,t)} r_ik` of resource `k` used at time `t`
(Eq. (2.1.2), p. 25). -/
noncomputable def Project.usage {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (t : ℝ) (k : K) : ℕ :=
  ∑ i ∈ P.activeSet S t, P.r i k

/-- Resource-feasibility of a schedule (Definition 2.1.1 with the resource constraints (2.1.4),
p. 25): `r_k(S, t) ≤ R_k` for every resource `k` and **every time `t ≥ 0`** (the book's (2.1.4)
writes `0 ≤ t ≤ d̄`; the book's proofs and Remark 2.3.11 use all `t ≥ 0`, which is the reading
adopted here). -/
def Project.IsResourceFeasible {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) :
    Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ k : K, P.usage S t k ≤ P.R k

/-- A feasible schedule (Definition 2.1.1, p. 25): time-feasible and resource-feasible; the set
`𝒮 = 𝒮_T ∩ 𝒮_R`. -/
def Project.IsFeasible {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  P.IsTimeFeasible S ∧ P.IsResourceFeasible S

/-- A forbidden set (Definition 2.3.9, Eq. (2.3.1), p. 34): a set `F ⊆ V` with
`∑_{i ∈ F} r_ik > R_k` for some resource `k`. -/
def Project.IsForbidden {n : ℕ} {K : Type} (P : Project n K) (F : Finset (Fin (n + 2))) : Prop :=
  ∃ k : K, P.R k < ∑ i ∈ F, P.r i k

/-- A minimal forbidden set (Definition 2.3.9, p. 34): a forbidden set no proper subset of which
is forbidden. The set `ℱ` of the book is `{F | P.IsMinimalForbidden F}`. -/
def Project.IsMinimalForbidden {n : ℕ} {K : Type} (P : Project n K)
    (F : Finset (Fin (n + 2))) : Prop :=
  Minimal P.IsForbidden F

end ProjSchedTW.OrderPolyhedra


