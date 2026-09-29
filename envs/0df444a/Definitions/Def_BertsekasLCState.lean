-- Prove2me | Definitions.Def_BertsekasLCState
-- name    : BertsekasLCState
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-06T05:10:11.688503+00:00
-- url     : https://prove2.me/theorems/1ab37c57-5fda-48f9-9601-e4dd96fef131
-- title:
--   The label correcting algorithm: state, initialization, and step relation
-- statement:
--   This module formalizes the **label correcting algorithm** of Bertsekas, Vol. I, §2.3.1, as a small-step transition system, so that its correctness can be proved for every execution rather than for one scheduling discipline.
--
--   **State.** An algorithm state consists of node labels $d_j \in \overline{\mathbb{R}}$, the scalar $\mathrm{UPPER}$ (which tracks the label of the destination $t$), and the candidate list $\mathrm{OPEN}$, a finite set of nodes.
--
--   **Initialization.** The run starts from
--
--   $$d_s = 0, \qquad d_j = +\infty \ \ (j \ne s), \qquad \mathrm{UPPER} = +\infty, \qquad \mathrm{OPEN} = \{s\}.$$
--
--   **One iteration.** Remove some node $i$ from $\mathrm{OPEN}$, then process each child $j$ of $i$ in turn (Step 2 of the source): if
--
--   $$d_i + a_{ij} \;<\; \min\{\, d_j, \; \mathrm{UPPER} \,\},$$
--
--   set $d_j := d_i + a_{ij}$; if in addition $j \ne t$, place $j$ in $\mathrm{OPEN}$, while if $j = t$, set $\mathrm{UPPER}$ to the new value. Otherwise nothing changes. The algorithm stops when $\mathrm{OPEN}$ is empty.
--
--   Because both the choice of $i$ and the order in which the children are processed are left open, a single relation captures a whole family of concrete methods — breadth-first, depth-first, best-first (Dijkstra), small-label-first — and a theorem proved about it holds for all of them at once.
--
--   **Formalization Note** One iteration is a relation, not a function: it existentially quantifies over the node removed from $\mathrm{OPEN}$ and over a permutation of that node's children, and the children are processed by a left-to-right fold, so each test sees the labels already updated by the children processed before it. Duplicate children collapse, since the children are collected as a finite set. A run is a chain of such steps from the initial state, and termination means reaching a state whose $\mathrm{OPEN}$ is empty.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 2.3.1; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 2.3.1, Step 2; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 2.3.1, Steps 1-3

import Mathlib
import Definitions.Def_BertsekasSPGraph

/-- The state of the label correcting algorithm of Section 2.3.1: the node
labels `label` (extended reals, `⊤` meaning "no path found yet"), the variable
`upper` (`UPPER`, the label of the destination), and the candidate list
`openList` (`OPEN`). -/
structure BertsekasLCState (V : Type) [Fintype V] [DecidableEq V] where
  label : V → EReal
  upper : EReal
  openList : Finset V

/-- The initial state of the label correcting algorithm: `d_s = 0`, `d_j = ∞`
for `j ≠ s`, `UPPER = ∞`, and `OPEN = {s}`. -/
noncomputable def BertsekasLCInit {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) : BertsekasLCState V :=
  { label := fun v => if v = G.s then 0 else ⊤
    upper := ⊤
    openList := {G.s} }

open Classical in
/-- Step 2 of the label correcting algorithm, for a single child `j` of the node
`i` just removed from `OPEN`: if `d_i + a_{ij} < min {d_j, UPPER}`, set
`d_j := d_i + a_{ij}`; in addition, if `j ≠ t` place `j` in `OPEN`, while if
`j = t` set `UPPER` to the new value `d_i + a_{it}` of `d_t`. -/
noncomputable def BertsekasLCProcessChild {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) (i : V) (σ : BertsekasLCState V) (j : V) :
    BertsekasLCState V :=
  if (i, j) ∈ G.arcs ∧
      σ.label i + (G.length i j : EReal) < min (σ.label j) σ.upper then
    { label := Function.update σ.label j (σ.label i + (G.length i j : EReal))
      upper := if j = G.t then σ.label i + (G.length i j : EReal) else σ.upper
      openList := if j = G.t then σ.openList else insert j σ.openList }
  else σ

open Classical in
/-- One iteration of the label correcting algorithm (Steps 1-2 of Section 2.3.1):
remove a node `i` from `OPEN` and execute Step 2
(`BertsekasLCProcessChild`) for each child `j` of `i`, in some order.
The relation is nondeterministic in the choice of `i` and in the order in which
the children are processed. -/
noncomputable def BertsekasLCStep {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) (σ σ' : BertsekasLCState V) : Prop :=
  ∃ i ∈ σ.openList, ∃ js : List V,
    js.Perm (((G.arcs.filter fun a => a.1 = i).image Prod.snd).toList) ∧
    σ' = js.foldl (BertsekasLCProcessChild G i)
      { σ with openList := σ.openList.erase i }


