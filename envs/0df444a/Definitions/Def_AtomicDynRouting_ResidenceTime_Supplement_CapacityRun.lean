-- Prove2me | Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_CapacityRun
-- name    : AtomicDynRouting_ResidenceTime_Supplement_CapacityRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:31:03.815614+00:00
-- url     : https://prove2.me/theorems/a5d7ba54-6546-4f24-944e-44dd8849d15e
-- title:
--   §4, p. 10 — atomic dynamic routing on the uniform-capacity network $G_c$
-- statement:
--   Let $G=(V,E)$ be a finite directed multigraph and $c$ a positive integer. The network $G_c$ has the vertices and edges of $G$, unit edge lengths, and capacity $c$ on every edge. An **atomic dynamic routing on $G_c$** is given by the data of the base model (entry times, routes, origins, destinations and the time at which each agent leaves each buffer of his route) subject to:
--
--   1. every route is a nonempty $o_i$-$d_i$ path of $G$;
--   2. finitely many agents enter at each integer time;
--   3. an agent leaves a buffer no earlier than he enters it;
--   4. at every integer time $s$ and for every edge $e$, exactly
--   $$n_s(U)=\min\{c,n\}$$
--   agents leave the buffer $U$ of $e$, where $n$ is the number of agents in $U$ at time $s$.
--
--   Condition (A1) (an agent enters the next buffer as soon as he reaches a vertex) and the unit transit time are built into the base model; the $n_s(U)$ leavers reach the head of $e$ at time $s+1$. No rule selects which agents leave. For $c=1$ this is the unit-capacity model of the base mission.
--
--   **Formalization Note** The number of agents in a buffer is counted as the number of pairs (agent, position on his route) whose edge is $e$; in an acyclic network a route passes each edge at most once, so this is the number of agents.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 10 (PDF 11), §4, definition of G_c and the relaxed (A2)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Model

namespace AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

variable {ι E V : Type}

/-- The number of agents in the buffer of edge `e` at the integer time `s`, counted as pairs
`(i, j)` such that agent `i` is in the buffer of the `j`-th edge of his route and that edge is `e`.
In an acyclic network a route passes `e` at most once, so this is the number of agents in the buffer.
The set is finite when finitely many agents enter at each time (clause 2 of `IsADRc`). -/
noncomputable def bufCount (R : RunData ι E V) (e : E) (s : ℕ) : ℕ :=
  {p : ι × ℕ | R.inBuf p.1 p.2 s ∧ (R.route p.1)[p.2]? = some e}.ncard

/-- The number of agents leaving the buffer of edge `e` at the integer time `s`. -/
noncomputable def leaveCount (R : RunData ι E V) (e : E) (s : ℕ) : ℕ :=
  {p : ι × ℕ | p.2 < (R.route p.1).length ∧ (R.route p.1)[p.2]? = some e ∧
    R.leave p.1 p.2 = (s : ℕ∞)}.ncard

/-- `IsADRc N c R`: the data `R` form an atomic dynamic routing on the network `G_c` of §4 (p. 10),
which has the vertices and edges of `N`, unit edge lengths, and capacity `c` on every edge:
1. every route is a nonempty `orig i`-`dest i` path of `N`;
2. finitely many agents enter at each integer time (§2.2);
3. an agent leaves a buffer no earlier than he enters it;
4. (A2) relaxed to capacity `c` (§4, p. 10): at each integer time `s`, exactly
   `n_s(U) = min{c, n}` agents leave the buffer `U` of each edge `e`, where `n` is the number of
   agents in `U` at time `s`. No rule selects which agents leave.
Unit transit times and (A1) (an agent enters the next buffer as soon as he reaches a vertex; the
`n_s(U)` leavers reach the head at `s + 1`) are built into `RunData.arrive`, exactly as in the base
`IsADR`, which is the case `c = 1` of this predicate. -/
def IsADRc (N : Network V E) (c : ℕ) (R : RunData ι E V) : Prop :=
  (∀ i, N.IsPathFrom (R.orig i) (R.dest i) (R.route i) ∧ R.route i ≠ []) ∧
  (∀ t : ℕ, {i | R.entry i = t}.Finite) ∧
  (∀ i j, j < (R.route i).length → R.arrive i j ≤ R.leave i j) ∧
  (∀ (e : E) (s : ℕ), leaveCount R e s = min c (bufCount R e s))

end AtomicDynRouting.ResidenceTime.Supplement


