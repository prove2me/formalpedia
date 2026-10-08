-- Prove2me | Definitions.Def_ProjSchedTW_Cumulative_Model
-- name    : ProjSchedTW_Cumulative_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T23:34:22.752002+00:00
-- url     : https://prove2.me/theorems/a58d8337-f106-4c97-8206-08f2183b338e
-- title:
--   §2.12.1 — projects with discrete cumulative resources, inventory profiles, surplus and shortage sets
-- statement:
--   This file sets up the model of §2.12.1 (discrete cumulative resources) of Neumann, Schwindt and Zimmermann.
--
--   **Project.** The activities are $V=\{0,1,\dots,n+1\}$ with $n\ge 1$; activity $0$ is the project beginning and $n+1$ the project completion. Each activity $i$ has an integer duration $p_i\ge 0$, with $p_0=p_{n+1}=0$ and $p_i>0$ for the real activities $i=1,\dots,n$. For each (discrete) cumulative resource $k\in\mathcal R^\gamma$ there are integer demands $r_{ik}\in\mathbb Z$, a safety stock $\underline R_k\in\mathbb Z$ and a storage capacity $\overline R_k\in\mathbb Z$. A negative demand $r_{ik}<0$ depletes $-r_{ik}$ units at the start of $i$, a positive demand $r_{ik}>0$ replenishes $r_{ik}$ units at the completion of $i$, and $r_{0k}$ is the initial stock. Write $V_k^-=\{i\mid r_{ik}<0\}$ and $V_k^+=\{i\mid r_{ik}>0\}$.
--
--   **Schedules and inventories.** A schedule is a vector of real start times $S=(S_i)_{i\in V}$ with $S_0=0$ and $S_i\ge 0$. The active set and the inventory of resource $k$ at time $t\ge 0$ are
--   $$
--   \mathcal A_k(S,t)=\{i\in V_k^-\mid S_i\le t\}\cup\{i\in V_k^+\mid S_i+p_i\le t\},\qquad r_k(S,t)=\sum_{i\in\mathcal A_k(S,t)} r_{ik}.
--   $$
--   $S$ is **inventory-feasible** if $\underline R_k\le r_k(S,t)\le\overline R_k$ for every resource $k$ and every $t\ge 0$ (inventory constraints (2.12.2)).
--
--   **Standing assumptions**, stated as named predicates: (2.12.1) $\underline R_k\le\sum_{i\in V} r_{ik}\le\overline R_k$ for all $k$, and Remark 2.12.2, $\underline R_k\le 0\le\overline R_k$ for all $k$.
--
--   **Forbidden sets.** A nonempty $F\subseteq V$ is a $k$-surplus set if $\sum_{i\in F}r_{ik}>\overline R_k$ and a $k$-shortage set if $\sum_{i\in F}r_{ik}<\underline R_k$. A $k$-surplus set $F$ is **minimal** if there is no $k$-surplus set $F'\subsetneq F$ with $F\setminus F'\subseteq V_k^+$ and no $k$-surplus set $F''\supsetneq F$ with $F''\setminus F\subseteq V_k^-$; minimal $k$-shortage sets are defined with the roles of $V_k^+$ and $V_k^-$ exchanged. This one-sided notion is not inclusion-minimality.
--
--   **Resolution conditions** (Theorem 2.12.4). Condition (a): for every resource $k$ and every minimal $k$-surplus set $F$ there are $j\in F$ and $i\notin F$ with $r_{jk}>0$, $r_{ik}<0$ and $S_j+p_j\ge S_i$. Condition (b): for every minimal $k$-shortage set $F$ there are $j\in F$, $i\notin F$ with $r_{jk}<0$, $r_{ik}>0$ and $S_j\ge S_i+p_i$.
--
--   **Shifted instance.** Given integers $(a_k)$, the shifted instance adds $a_k$ to $r_{0k}$, $\underline R_k$ and $\overline R_k$ and leaves everything else unchanged (p. 131).
--
--   These objects are the common vocabulary of the mission: the goal theorem characterizes inventory-feasibility by conditions (a) and (b).
--
--   **Formalization Note** Activities are `Fin (n + 2)`, activity $n+1$ is `Fin.last (n + 1)`; resources form an arbitrary type `K`. Demands and bounds are integers, start times are reals. The inventory constraints are required for every $t\ge 0$, not only for $0\le t\le\bar d$ as (2.12.2) is printed; the book's proof of Theorem 2.12.4 works with arbitrary $t\ge 0$. Time lags and arcs of the project network are omitted because no statement of this mission uses them; schedules are not required to be time-feasible. The book's $\overline R_k\ge\underline R_k$ is not a field; it follows from (2.12.1). Proper inclusions are `⊂` on `Finset`.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 129–131, §2.12.1, Eqs. (2.12.1), (2.12.2), definitions of A_k(S,t), r_k(S,t), k-surplus and k-shortage sets, Remark 2.12.2; pp. 132–133, conditions (a), (b) of Theorem 2.12.4

import Mathlib

namespace ProjSchedTW.Cumulative

/-- A project with discrete cumulative resources (Neumann, Schwindt & Zimmermann, §1.1 and
§2.12.1, pp. 129–130). Activities are `V = {0, 1, …, n+1}` = `Fin (n + 2)`, with `0` the project
beginning and `Fin.last (n+1)` the project completion; `K` indexes the cumulative resources
`ℛ^γ`. `r i k` is the demand of activity `i` for resource `k`: `r i k < 0` depletes `-r i k` units
at the start `S i`, `r i k > 0` replenishes `r i k` units at the completion `S i + p i`, and `r 0 k`
is the initial stock. `Rlow k` is the safety stock `R̲_k`, `Rup k` the storage capacity `R̄_k`. -/
structure CumulativeProject (n : ℕ) (K : Type) where
  /-- durations `p_i` -/
  p : Fin (n + 2) → ℕ
  /-- demands `r_ik` for cumulative resources -/
  r : Fin (n + 2) → K → ℤ
  /-- safety stock `R̲_k` -/
  Rlow : K → ℤ
  /-- storage capacity `R̄_k` -/
  Rup : K → ℤ
  /-- at least one real activity (§1.1) -/
  one_le_n : 1 ≤ n
  /-- the project beginning has duration zero -/
  p_zero : p 0 = 0
  /-- the project completion has duration zero -/
  p_last : p (Fin.last (n + 1)) = 0
  /-- real activities have positive durations -/
  p_pos : ∀ i : Fin (n + 2), i ≠ 0 → i ≠ Fin.last (n + 1) → 0 < p i

variable {n : ℕ} {K : Type}

/-- A schedule: real start times with `S_0 = 0` and `S_i ≥ 0` for every activity. -/
def IsSchedule (S : Fin (n + 2) → ℝ) : Prop :=
  S 0 = 0 ∧ ∀ i, 0 ≤ S i

/-- The active set `A_k(S,t) = {i ∈ V_k⁻ | S_i ≤ t} ∪ {i ∈ V_k⁺ | S_i + p_i ≤ t}` of activities
that have used cumulative resource `k` by time `t` (p. 129). -/
noncomputable def activeSet (P : CumulativeProject n K) (S : Fin (n + 2) → ℝ) (k : K) (t : ℝ) :
    Finset (Fin (n + 2)) :=
  Finset.univ.filter (fun i => (P.r i k < 0 ∧ S i ≤ t) ∨ (0 < P.r i k ∧ S i + (P.p i : ℝ) ≤ t))

/-- The inventory `r_k(S,t) = ∑_{i ∈ A_k(S,t)} r_ik` of resource `k` at time `t` (pp. 129–130). -/
noncomputable def inventory (P : CumulativeProject n K) (S : Fin (n + 2) → ℝ) (k : K) (t : ℝ) : ℤ :=
  ∑ i ∈ activeSet P S k t, P.r i k

/-- Inventory-feasibility, (2.12.2), read for every `t ≥ 0`:
`R̲_k ≤ r_k(S,t) ≤ R̄_k` for all resources `k` and all `t ≥ 0`. -/
def InventoryFeasible (P : CumulativeProject n K) (S : Fin (n + 2) → ℝ) : Prop :=
  ∀ k : K, ∀ t : ℝ, 0 ≤ t → P.Rlow k ≤ inventory P S k t ∧ inventory P S k t ≤ P.Rup k

/-- Standing assumption (2.12.1): `R̲_k ≤ ∑_{i ∈ V} r_ik ≤ R̄_k` for every resource `k`. -/
def TotalDemandWithinBounds (P : CumulativeProject n K) : Prop :=
  ∀ k : K, P.Rlow k ≤ ∑ i, P.r i k ∧ ∑ i, P.r i k ≤ P.Rup k

/-- Remark 2.12.2: `R̲_k ≤ 0` and `R̄_k ≥ 0` for every resource `k`. -/
def BoundsStraddleZero (P : CumulativeProject n K) : Prop :=
  ∀ k : K, P.Rlow k ≤ 0 ∧ 0 ≤ P.Rup k

/-- A `k`-surplus set: a nonempty `F ⊆ V` with `∑_{i ∈ F} r_ik > R̄_k` (p. 131). -/
def IsSurplusSet (P : CumulativeProject n K) (k : K) (F : Finset (Fin (n + 2))) : Prop :=
  F.Nonempty ∧ P.Rup k < ∑ i ∈ F, P.r i k

/-- A `k`-shortage set: a nonempty `F ⊆ V` with `∑_{i ∈ F} r_ik < R̲_k` (p. 131). -/
def IsShortageSet (P : CumulativeProject n K) (k : K) (F : Finset (Fin (n + 2))) : Prop :=
  F.Nonempty ∧ ∑ i ∈ F, P.r i k < P.Rlow k

/-- A minimal `k`-surplus set (p. 131): a `k`-surplus set `F` such that there is no `k`-surplus set
`F' ⊂ F` with `F \ F' ⊆ V_k⁺` and no `k`-surplus set `F'' ⊃ F` with `F'' \ F ⊆ V_k⁻`.
(`⊂`, `⊃` are proper inclusions.) This is not inclusion-minimality. -/
def IsMinimalSurplusSet (P : CumulativeProject n K) (k : K) (F : Finset (Fin (n + 2))) : Prop :=
  IsSurplusSet P k F ∧
    (¬ ∃ F' : Finset (Fin (n + 2)), F' ⊂ F ∧ IsSurplusSet P k F' ∧ ∀ j ∈ F \ F', 0 < P.r j k) ∧
    (¬ ∃ F'' : Finset (Fin (n + 2)), F ⊂ F'' ∧ IsSurplusSet P k F'' ∧ ∀ j ∈ F'' \ F, P.r j k < 0)

/-- A minimal `k`-shortage set (p. 131): a `k`-shortage set `F` such that there is no `k`-shortage
set `F' ⊂ F` with `F \ F' ⊆ V_k⁻` and no `k`-shortage set `F'' ⊃ F` with `F'' \ F ⊆ V_k⁺`. -/
def IsMinimalShortageSet (P : CumulativeProject n K) (k : K) (F : Finset (Fin (n + 2))) : Prop :=
  IsShortageSet P k F ∧
    (¬ ∃ F' : Finset (Fin (n + 2)), F' ⊂ F ∧ IsShortageSet P k F' ∧ ∀ j ∈ F \ F', P.r j k < 0) ∧
    (¬ ∃ F'' : Finset (Fin (n + 2)), F ⊂ F'' ∧ IsShortageSet P k F'' ∧ ∀ j ∈ F'' \ F, 0 < P.r j k)

/-- Condition (a) of Theorem 2.12.4: every minimal `k`-surplus set `F` contains a replenishing
activity `j` that is completed no earlier than some depleting activity `i ∉ F` is started,
`S_j + p_j ≥ S_i`. -/
def ResolvesSurplusSets (P : CumulativeProject n K) (S : Fin (n + 2) → ℝ) : Prop :=
  ∀ k : K, ∀ F : Finset (Fin (n + 2)), IsMinimalSurplusSet P k F →
    ∃ j ∈ F, ∃ i ∉ F, 0 < P.r j k ∧ P.r i k < 0 ∧ S i ≤ S j + (P.p j : ℝ)

/-- Condition (b) of Theorem 2.12.4: every minimal `k`-shortage set `F` contains a depleting
activity `j` that starts no earlier than some replenishing activity `i ∉ F` is completed,
`S_j ≥ S_i + p_i`. -/
def ResolvesShortageSets (P : CumulativeProject n K) (S : Fin (n + 2) → ℝ) : Prop :=
  ∀ k : K, ∀ F : Finset (Fin (n + 2)), IsMinimalShortageSet P k F →
    ∃ j ∈ F, ∃ i ∉ F, P.r j k < 0 ∧ 0 < P.r i k ∧ S i + (P.p i : ℝ) ≤ S j

/-- The instance obtained by adding the same integer `a_k` to the initial inventory `r_0k`, the
safety stock `R̲_k` and the storage capacity `R̄_k` of every resource `k` (p. 131). -/
def shiftStock (P : CumulativeProject n K) (a : K → ℤ) : CumulativeProject n K where
  p := P.p
  r := fun i k => if i = 0 then P.r i k + a k else P.r i k
  Rlow := fun k => P.Rlow k + a k
  Rup := fun k => P.Rup k + a k
  one_le_n := P.one_le_n
  p_zero := P.p_zero
  p_last := P.p_last
  p_pos := P.p_pos

end ProjSchedTW.Cumulative


