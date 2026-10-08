-- Prove2me | Definitions.Def_ProjSchedTW_Complexity_Cumulative
-- name    : ProjSchedTW_Complexity_Cumulative
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T01:52:42.485846+00:00
-- url     : https://prove2.me/theorems/0ad54a44-560a-401a-b567-c450b7123af9
-- title:
--   PSc|temp|C_max: projects with cumulative resources, feasible schedules, the feasibility language, and the PARTITION project
-- statement:
--   This file defines the decision problem of Theorem 2.12.1 of Neumann, Schwindt and Zimmermann: does a given project with discrete cumulative resources have a feasible schedule?
--
--   **Instances.** An instance of $PSc|temp|C_{\max}$ has activities $V=\{0,1,\dots,n+1\}$ ($0$ the project beginning, $n+1$ the project completion), durations $p_i\in\mathbb N$, a project network $N$ with arc set $E$ and integer arc weights $\delta_{ij}$, cumulative resources $k\in\mathcal R^\gamma=\{1,\dots,m\}$ with integer demands $r_{ik}$, safety stocks $\underline R_k\in\mathbb Z$ and storage capacities $\overline R_k\in\mathbb Z$. A demand $r_{ik}<0$ depletes $-r_{ik}$ units at the start of $i$; $r_{ik}>0$ replenishes $r_{ik}$ units at its completion; $r_{0k}$ is the initial stock. An instance is **well formed** if $n\ge1$, $p_0=p_{n+1}=0$, $N$ has no loops, $\underline R_k\le\overline R_k$, and (2.12.1) holds:
--   $$\underline R_k\le\sum_{i\in V} r_{ik}\le\overline R_k\qquad(k\in\mathcal R^\gamma).$$
--   The network is **acyclic** if its nodes can be numbered so that every arc goes from a smaller to a larger number.
--
--   **Schedules.** A schedule $S=(S_i)_{i\in V}$ of real start times is time-feasible if $S_0=0$, $S_i\ge0$ and $S_j-S_i\ge\delta_{ij}$ for all $\langle i,j\rangle\in E$. With the active set $\mathcal A_k(S,t)=\{i\mid r_{ik}<0,\ S_i\le t\}\cup\{i\mid r_{ik}>0,\ S_i+p_i\le t\}$ and the inventory $r_k(S,t)=\sum_{i\in\mathcal A_k(S,t)} r_{ik}$, $S$ is inventory-feasible if
--   $$\underline R_k\le r_k(S,t)\le\overline R_k\qquad(k\in\mathcal R^\gamma,\ t\ge0),$$
--   and feasible if it is time-feasible and inventory-feasible.
--
--   **Language.** Each instance is coded, in binary over $\{0,1,-,\#\}$, as the list $n, m$; $p_0,\dots,p_{n+1}$; for every ordered pair $(i,j)$ the arc indicator and $\delta_{ij}$; the demands $r_{ik}$; the $\underline R_k$; the $\overline R_k$. For a class $C$ of instances, the feasibility language is the set of codes of well-formed instances in $C$ that have a feasible schedule. $C=$ all instances gives the decision problem of $PSc|temp|C_{\max}$, $C=$ acyclic networks its restriction.
--
--   **The PARTITION project** (proof of Theorem 2.12.1). From sizes $s(1),\dots,s(\nu)$ it builds $n=\nu$ activities of duration zero, one cumulative resource with $r_0=r_{n+1}=-\sum_{i\in\mathcal I}s(i)/2$ and $r_i=s(i)$ for $i\in\mathcal I$, $\underline R=\overline R=0$, and arcs $\langle0,n+1\rangle$ with $d^{\min}_{0,n+1}=1$ and $\langle0,i\rangle$, $\langle i,n+1\rangle$ with weight $0$.
--
--   These objects carry the goal theorem and its milestones.
--
--   **Formalization Note** Activities are `Fin (n + 2)` with $n+1$ = `Fin.last (n + 1)`; resources are `Fin m`. Real activities may have duration $0$ (the reduction uses only such activities), unlike the standing $p_i>0$ of Chapter 2 for renewable resources. The inventory constraints are imposed for every $t\ge0$ rather than $0\le t\le\bar d$ as (2.12.2) is printed; this is the series-wide reading, used by the book's proofs. The arc set is a `Finset` of ordered pairs; the code lists $\delta_{ij}$ for all pairs, arcs or not. In the PARTITION project, $\sum s(i)/2$ is integer division; it is exact only when $\sum s(i)$ is even, and every statement using the project assumes that. Remark 2.12.2 ($\underline R_k\le0\le\overline R_k$) and the source/sink arcs of Remark 1.1.2 are not part of well-formedness.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 129–130, §2.12.1, Eqs. (2.12.1)–(2.12.3), active set A_k(S,t), inventory r_k(S,t); p. 131, the project of the proof of Theorem 2.12.1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace ProjSchedTW.Complexity

open CookPvsNP

/-- An instance of `PSc|temp|C_max`, the project scheduling problem with (discrete) cumulative
resources (Neumann, Schwindt & Zimmermann, §1.1–1.2 and §2.12.1, pp. 129–130).
Activities are `V = {0, 1, …, n+1}` = `Fin (n + 2)`: `0` is the project beginning and
`Fin.last (n + 1)` the project completion; the cumulative resources are `ℛ^γ = Fin m`.
* `p i ∈ ℕ` is the duration of activity `i` (zero durations are allowed);
* `E` is the arc set of the project network `N`, and `δ i j ∈ ℤ` the weight of arc `⟨i, j⟩`;
* `r i k ∈ ℤ` is the demand of activity `i` for resource `k`: `r i k < 0` depletes `-r i k` units
  at the start of `i`, `r i k > 0` replenishes `r i k` units at the completion of `i`;
* `Rlow k ∈ ℤ` is the safety stock `R̲_k` and `Rup k ∈ ℤ` the storage capacity `R̄_k`. -/
structure CumInstance where
  n : ℕ
  m : ℕ
  p : Fin (n + 2) → ℕ
  E : Finset (Fin (n + 2) × Fin (n + 2))
  δ : Fin (n + 2) → Fin (n + 2) → ℤ
  r : Fin (n + 2) → Fin m → ℤ
  Rlow : Fin m → ℤ
  Rup : Fin m → ℤ

namespace CumInstance

/-- The standing assumptions on an instance: at least one real activity (`n ≥ 1`, §1.1); the
fictitious activities `0` and `n+1` have duration `0`; the network has no loops;
`R̲_k ≤ R̄_k` (p. 129); and the total demand lies within the bounds,
`R̲_k ≤ ∑_{i ∈ V} r_ik ≤ R̄_k` (Eq. (2.12.1), p. 129). -/
def WellFormed (x : CumInstance) : Prop :=
  1 ≤ x.n ∧ x.p 0 = 0 ∧ x.p (Fin.last (x.n + 1)) = 0 ∧ (∀ e ∈ x.E, e.1 ≠ e.2) ∧
    (∀ k, x.Rlow k ≤ x.Rup k) ∧
    (∀ k, x.Rlow k ≤ ∑ i, x.r i k ∧ ∑ i, x.r i k ≤ x.Rup k)

/-- The project network `N` is acyclic: its nodes can be numbered so that every arc goes from a
smaller to a larger number (equivalently, `N` has no directed cycle). -/
def IsAcyclic (x : CumInstance) : Prop :=
  ∃ ord : Fin (x.n + 2) → ℕ, ∀ e ∈ x.E, ord e.1 < ord e.2

/-- A time-feasible schedule (Definition 1.3.1): real start times with `S_0 = 0`, `S_i ≥ 0`, and
`S_j - S_i ≥ δ_ij` for every arc `⟨i, j⟩ ∈ E` (Eq. (1.2.1)). -/
def TimeFeasible (x : CumInstance) (S : Fin (x.n + 2) → ℝ) : Prop :=
  S 0 = 0 ∧ (∀ i, 0 ≤ S i) ∧ ∀ e ∈ x.E, (x.δ e.1 e.2 : ℝ) ≤ S e.2 - S e.1

/-- The active set `A_k(S,t) = {i ∈ V_k⁻ | S_i ≤ t} ∪ {i ∈ V_k⁺ | S_i + p_i ≤ t}` (p. 129). -/
noncomputable def activeSet (x : CumInstance) (S : Fin (x.n + 2) → ℝ) (k : Fin x.m) (t : ℝ) :
    Finset (Fin (x.n + 2)) :=
  open Classical in
  Finset.univ.filter fun i => (x.r i k < 0 ∧ S i ≤ t) ∨ (0 < x.r i k ∧ S i + (x.p i : ℝ) ≤ t)

/-- The inventory `r_k(S,t) = ∑_{i ∈ A_k(S,t)} r_ik` of resource `k` at time `t` (p. 129). -/
noncomputable def inventory (x : CumInstance) (S : Fin (x.n + 2) → ℝ) (k : Fin x.m) (t : ℝ) : ℤ :=
  ∑ i ∈ x.activeSet S k t, x.r i k

/-- Inventory-feasibility, the inventory constraints (2.12.2) read for every `t ≥ 0`:
`R̲_k ≤ r_k(S,t) ≤ R̄_k` for all resources `k`. -/
def InventoryFeasible (x : CumInstance) (S : Fin (x.n + 2) → ℝ) : Prop :=
  ∀ k, ∀ t : ℝ, 0 ≤ t → x.Rlow k ≤ x.inventory S k t ∧ x.inventory S k t ≤ x.Rup k

/-- A feasible schedule (p. 130): time-feasible and inventory-feasible. -/
def Feasible (x : CumInstance) (S : Fin (x.n + 2) → ℝ) : Prop :=
  x.TimeFeasible S ∧ x.InventoryFeasible S

/-- The numbers describing an instance, in order: `n`, `m`; the durations `p_0, …, p_{n+1}`;
for every ordered pair `(i, j)` (row by row) the arc indicator (`1` if `⟨i, j⟩ ∈ E`, else `0`)
and the weight `δ_ij`; the demands `r_ik` (row by row); the safety stocks `R̲_k`; the storage
capacities `R̄_k`. -/
def code (x : CumInstance) : List ℤ :=
  [(x.n : ℤ), (x.m : ℤ)] ++ List.ofFn (fun i => (x.p i : ℤ)) ++
    (List.ofFn fun i => List.ofFn fun j =>
      [if (i, j) ∈ x.E then (1 : ℤ) else 0, x.δ i j]).flatten.flatten ++
    (List.ofFn fun i => List.ofFn fun k => x.r i k).flatten ++
    List.ofFn x.Rlow ++ List.ofFn x.Rup

/-- The binary code of an instance over the alphabet `BSym`. -/
def encode (x : CumInstance) : List BSym := encInts x.code

end CumInstance

/-- The feasibility language of `PSc|temp|C_max` restricted to the instances satisfying `C`:
the codes of well-formed instances satisfying `C` that admit a feasible schedule. With
`C := fun _ => True` it is the full decision problem; with `C := CumInstance.IsAcyclic` its
restriction to acyclic project networks. -/
def cumFeasLang (C : CumInstance → Prop) : Lang BSym :=
  { w | ∃ x : CumInstance, x.WellFormed ∧ C x ∧ (∃ S, x.Feasible S) ∧ w = x.encode }

/-- The size of real activity `j ∈ {1, …, ν}` of the PARTITION project: `s(j)`, where the
sizes are indexed `s : Fin ν → ℕ` and activity `j` carries `s(j - 1)` in that indexing; `0` for
the fictitious activities `0` and `ν + 1`. -/
def partitionSize {ν : ℕ} (s : Fin ν → ℕ) (j : Fin (ν + 2)) : ℕ :=
  if h : 0 < j.val ∧ j.val < ν + 1 then s ⟨j.val - 1, by omega⟩ else 0

/-- The project of the proof of Theorem 2.12.1 (p. 131) built from PARTITION sizes
`s(1), …, s(ν)`: `n = ν` activities of duration zero and one cumulative resource with
`r_0 = r_{n+1} = -∑_{i ∈ I} s(i)/2`, `r_i = s(i)` (`i ∈ I`), `R̲ = R̄ = 0`, and arcs
`⟨0, n+1⟩` with `d_{0,n+1}^min = 1` and `⟨0, i⟩`, `⟨i, n+1⟩` with weight `0` (`i ∈ I`).
The value `-∑ s(i)/2` uses integer division and is exact only when `∑ s(i)` is even. -/
def partitionProject {ν : ℕ} (s : Fin ν → ℕ) : CumInstance where
  n := ν
  m := 1
  p := fun _ => 0
  E := (Finset.univ.filter fun e : Fin (ν + 2) × Fin (ν + 2) =>
      (e.1 = 0 ∧ e.2 ≠ 0) ∨ (e.1 ≠ 0 ∧ e.1 ≠ Fin.last (ν + 1) ∧ e.2 = Fin.last (ν + 1)))
  δ := fun i j => if i = 0 ∧ j = Fin.last (ν + 1) then 1 else 0
  r := fun i _ => if i = 0 ∨ i = Fin.last (ν + 1) then -((∑ l, (s l : ℤ)) / 2)
    else (partitionSize s i : ℤ)
  Rlow := fun _ => 0
  Rup := fun _ => 0

end ProjSchedTW.Complexity


