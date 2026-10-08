-- Prove2me | Definitions.Def_ClarkeWright64_Savings_Procedure
-- name    : ClarkeWright64_Savings_Procedure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:39:23.816187+00:00
-- url     : https://prove2.me/theorems/35f38fdb-021a-497f-819f-4f130903dcf1
-- title:
--   Computational procedure, pp. 572–575 — states, the matrix t, conditions (I)–(III), linking, the max-saving step, termination
-- statement:
--   This module describes the savings procedure of Clarke and Wright (pp. 572–575) as a transition system on **states**, a state being a list of runs (ordered lists of customers).
--
--   1. A state is an **allocation** if no run is empty, no run visits the depot, and every customer $P_1,\dots,P_M$ lies on exactly one run exactly once.
--   2. The entries of the half matrix are read off a state: for customers $y\ne z$, $t_{y,z}=1$ if $P_y$ and $P_z$ are consecutive on some run and $0$ otherwise; $t_{y,0}$ is the number of runs that start at $P_y$ plus the number that end at $P_y$, so a customer served alone by a truck has $t_{y,0}=2$.
--   3. The **initial basic solution** sends one truck to each customer: the runs $[P_1],\dots,[P_M]$.
--   4. $Q_y$ is the total load on the run through $P_y$.
--   5. A cell $(y:z)$ of two distinct customers is **admissible** if (I) $t_{y,0}>0$ and $t_{z,0}>0$; (II) $P_y$ and $P_z$ are not on the same run; (III) after the runs through $P_y$ and $P_z$ are replaced by one run of load $Q_y+Q_z$, the run loads pass the Table II test.
--   6. **Linking** $(y:z)$ removes the run $R$ through $P_y$ and the run $R'$ through $P_z$ and adds the run that traverses $R$ ending at $P_y$, then $R'$ starting at $P_z$.
--   7. A **step** links an admissible cell whose saving $d_{0,y}+d_{0,z}-d_{y,z}$ is maximal among all admissible cells. Ties are broken arbitrarily, as the paper suggests choosing randomly, so a step is a relation and not a function.
--   8. A state is **terminal** when no cell is admissible ("no more links are possible"), and **reachable** when some sequence of steps leads to it from the initial basic solution.
--   9. The **optimum** of the problem of p. 568 is the infimum of the mileages of the allocations whose run loads are fleet feasible.
--
--   **Formalization Note** No positivity condition is placed on the saving: the paper links the maximum admissible saving and stops only when no link is possible. A run is reversed when necessary so that $P_y$ and $P_z$ become adjacent; this is why the theorems about mileage assume symmetric distances. `t` is computed from the runs rather than stored, so relation (A) is a theorem about reachable states. The optimum is a real infimum; it is meaningful when some allocation is feasible (the set is then finite and nonempty).
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), pp. 572–575, Computational procedure (conditions (I)–(III), relation (A)); p. 568 (the problem)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance

namespace ClarkeWright64.Savings

open Classical

variable {M n : ℕ}

/-- A state of the computational procedure (pp. 572–575): the list of truck runs, each run the
ordered list of customers visited between leaving and re-entering the depot. -/
abbrev State (M : ℕ) := List (List (Fin (M + 1)))

/-- The customers `P₁, …, P_M`, in increasing order. -/
def customers (M : ℕ) : List (Fin (M + 1)) :=
  (List.finRange (M + 1)).filter (fun j => j ≠ 0)

/-- A state is an allocation of the customers to runs: no run is empty, no run visits the depot,
and every customer lies on exactly one run exactly once. -/
def IsAllocation (s : State M) : Prop :=
  (∀ r ∈ s, r ≠ [] ∧ (0 : Fin (M + 1)) ∉ r) ∧ s.flatten.Perm (customers M)

/-- The entries `t_{y,z}` of the half matrix, p. 573, read off a state.
* For customers `y ≠ z`: `t_{y,z} = 1` if `P_y` and `P_z` are consecutive on some run (in either
  order), and `0` otherwise.
* `t_{y,0}` (and `t_{0,y}`) for a customer `y`: the number of runs that start at `y` plus the
  number that end at `y`; a customer served alone by a truck has `t_{y,0} = 2`.
* The diagonal is `0`. -/
noncomputable def t (s : State M) (y z : Fin (M + 1)) : ℕ :=
  if y = z then 0
  else if z = 0 then s.countP (fun r => decide (r.head? = some y)) +
    s.countP (fun r => decide (r.getLast? = some y))
  else if y = 0 then s.countP (fun r => decide (r.head? = some z)) +
    s.countP (fun r => decide (r.getLast? = some z))
  else if ∃ r ∈ s, [y, z] <:+: r ∨ [z, y] <:+: r then 1 else 0

/-- The initial basic solution, p. 573: one truck to each customer, `t_{y,0} = 2`
(`y = 1, …, M`). -/
def init (M : ℕ) : State M :=
  (customers M).map (fun j => [j])

/-- The entry `Q_y` of the column vector `Q` (pp. 573, 575): the total load of the run on which
`P_y` lies (`0` if there is none). -/
noncomputable def Q (I : Instance M n) (s : State M) (y : Fin (M + 1)) : ℝ :=
  ((s.find? (fun r => decide (y ∈ r))).map I.runLoad).getD 0

/-- The run loads after the amendment of condition (III), p. 573: the runs through `P_y` and
`P_z` are removed and replaced by one run carrying `Q_y + Q_z`. -/
noncomputable def amendedLoads (I : Instance M n) (s : State M) (y z : Fin (M + 1)) :
    Multiset ℝ :=
  ↑((s.filter (fun r => decide (y ∉ r ∧ z ∉ r))).map I.runLoad ++ [Q I s y + Q I s z])

/-- Cell `(y:z)` may be linked (p. 573): `y, z` are distinct customers and
(I) `t_{y,0} > 0` and `t_{z,0} > 0`;
(II) `P_y` and `P_z` are not already on the same run;
(III) the amended run loads pass the Table II test. -/
def Admissible (I : Instance M n) (s : State M) (y z : Fin (M + 1)) : Prop :=
  y ≠ 0 ∧ z ≠ 0 ∧ y ≠ z ∧
    0 < t s y 0 ∧ 0 < t s z 0 ∧
    (¬ ∃ r ∈ s, y ∈ r ∧ z ∈ r) ∧
    I.TableIIOK (amendedLoads I s y z)

/-- A run oriented so that it ends at `y` (reversed unless its last customer is `y`). -/
def orientEnd (r : List (Fin (M + 1))) (y : Fin (M + 1)) : List (Fin (M + 1)) :=
  if r.getLast? = some y then r else r.reverse

/-- A run oriented so that it starts at `z` (reversed unless its first customer is `z`). -/
def orientStart (r : List (Fin (M + 1))) (z : Fin (M + 1)) : List (Fin (M + 1)) :=
  if r.head? = some z then r else r.reverse

/-- Linking cell `(y:z)`, p. 575 (`t_{y,z}` is made `1`, the other `t_{i,j}` amended subject to
relation (A)): the run `R` through `P_y` and the run `R'` through `P_z` are removed, and the single
run `…, P_y, P_z, …` (`R` oriented to end at `y`, followed by `R'` oriented to start at `z`) is
added. -/
def link (s : State M) (y z : Fin (M + 1)) : State M :=
  match s.find? (fun r => decide (y ∈ r)), s.find? (fun r => decide (z ∈ r)) with
  | some R, some R' =>
      s.filter (fun r => decide (y ∉ r ∧ z ∉ r)) ++ [orientEnd R y ++ orientStart R' z]
  | _, _ => s

/-- One iteration of the procedure, pp. 573–575: some admissible cell `(y:z)` of maximum saving
among all admissible cells is linked. Ties may be broken in any way ("one of these be selected
randomly", p. 575), so this is a relation. -/
def Step (I : Instance M n) (s s' : State M) : Prop :=
  ∃ y z, Admissible I s y z ∧
    (∀ y' z', Admissible I s y' z' → I.saving y' z' ≤ I.saving y z) ∧ s' = link s y z

/-- The procedure stops: "no more links are possible" (p. 575). -/
def Terminal (I : Instance M n) (s : State M) : Prop :=
  ¬ ∃ y z, Admissible I s y z

/-- The states some run of the procedure reaches from the initial basic solution. -/
def Reachable (I : Instance M n) (s : State M) : Prop :=
  Relation.ReflTransGen (Step I) (init M) s

/-- The optimum of the problem of p. 568: the least total mileage of an allocation of the
customers to runs whose loads can be carried by the available trucks. -/
noncomputable def optMileage (I : Instance M n) : ℝ :=
  sInf {m | ∃ s : State M, IsAllocation s ∧ I.FleetFeasible ↑(s.map I.runLoad) ∧
    m = I.mileage s}

end ClarkeWright64.Savings


