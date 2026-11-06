-- Prove2me | Definitions.Def_NearLinIsing_chain
-- name    : NearLinIsing_chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:43:15.859204+00:00
-- url     : https://prove2.me/theorems/8acf02c5-c4d7-4e83-97ec-d34fe0344b9c
-- title:
--   The simulation of the insertion–deletion chain on cycle polymers
-- statement:
--   One step draws $U$. If $U<|E(H)|/(4N)$ it runs a cycle trial and inserts the output cycle when all of its ports are free. Otherwise, if $U<|E(H)|/(4N)+1/4$, it chooses $j$ uniformly from the $N$ indices and deletes the $j$-th present cycle if the family has that many members. Otherwise it keeps the family. The state holds the occupied ports of $H$, the edge list of each present cycle, and the trial's scratch arrays.
--
--   `simulateChain` constructs the port graph and runs $t$ steps from the empty family.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, §3.1, p. 10; Lemma 4.4, p. 21; Proposition 4.6 and its proof, pp. 21–22

import Mathlib
import Definitions.Def_NearLinIsing_buildPort
import Definitions.Def_NearLinIsing_cycleTrial

namespace NearLinIsing

/-!
The simulation of the insertion–deletion chain on cycle polymers of `H` (§3.1, p. 10; Lemma 4.4;
proof of Proposition 4.6, pp. 21–22).

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, §3.1 (p. 10), Lemma 4.4 (p. 21), Proposition 4.6 and its proof
(pp. 21–22).
-/

/-- The state of the chain simulation: `occ` marks the occupied ports of `H` (the "owner" array of
the proof of Proposition 4.6, as occupied flags), `fam` stores the edge list of every present
cycle (the deletion list), `sc` holds the trial's scratch arrays. -/
structure ChainState where
  occ : Array Bool
  fam : Array (List ℕ)
  sc : Scratch

/-- **One step of the chain** `P` of §3.1, p. 10, on cycle polymers of `H` with size parameter
`N`. Draw `U`.
(i) If `U < |E(H)|/(4N)`, run one cycle trial (Lemma 4.4); insert its output cycle if all its
ports are free.
(ii) Else, if `U < |E(H)|/(4N) + 1/4`, choose `j` uniformly from the `N` indices and delete the
`j`-th present cycle if the family has more than `j` members (`j` counted from `0`).
(iii) Otherwise keep the family. -/
noncomputable def chainStep (H : PortGraph) (N : ℕ) (st : ChainState) : Prog ChainState := do
  let u ← drawU
  tick 5 -- two casts, multiplication, division, comparison
  let p : ℝ := (H.ne : ℝ) / (4 * N)
  if u < p then
    let tr ← cycleTrial H st.sc
    match tr.1 with
    | none => return { st with sc := tr.2 }
    | some C =>
      let mut ok := true
      for e in C do
        tick 6 -- dispatch, two endpoint reads, two flag reads, disjunction
        if st.occ[H.eU[e]!]! || st.occ[H.eV[e]!]! then ok := false
      tick 1 -- branch
      if ok then
        let mut occ := st.occ
        for e in C do
          tick 5 -- dispatch, two endpoint reads, two writes
          occ := (occ.set! H.eU[e]! true).set! H.eV[e]! true
        tick 1 -- push
        return { occ := occ, fam := st.fam.push C, sc := tr.2 }
      else
        return { st with sc := tr.2 }
  else
    tick 2 -- addition, comparison
    if u < p + 1 / 4 then
      let j ← uniformIdx N
      tick 2 -- size read, comparison
      if j < st.fam.size then
        tick 1 -- read the deletion list
        let C := st.fam[j]!
        let mut occ := st.occ
        for e in C do
          tick 5 -- dispatch, two endpoint reads, two writes
          occ := (occ.set! H.eU[e]! false).set! H.eV[e]! false
        tick 3 -- read last slot, write slot j, pop
        return { st with occ := occ, fam := (st.fam.set! j st.fam.back!).pop }
      else
        return st
    else
      return st

/-- The initial state: the empty family and clean arrays (allocation charged). -/
def initState (H : PortGraph) : Prog ChainState := do
  tick (H.np + 2 * H.ne + H.np) -- allocate occ, vis, mark
  return { occ := Array.replicate H.np false, fam := #[], sc := Scratch.init H }

/-- Run `t` steps of the chain from the empty family. -/
noncomputable def runSteps (H : PortGraph) (N t : ℕ) : Prog ChainState := do
  let mut st ← initState H
  for _ in List.range t do
    tick 1 -- dispatch
    st ← chainStep H N st
  return st

/-- **The simulation of Proposition 4.6** (proof, pp. 21–22): construct the port graph, then run `t`
chain steps from `∅`. Returns `H` and the final family (edge lists). -/
noncomputable def simulateChain (G : IncGraph) (r : ℝ) (N t : ℕ) :
    Prog (PortGraph × Array (List ℕ)) := do
  let H ← buildPort G r
  let st ← runSteps H N t
  return (H, st.fam)

/-- The family of edge sets named by a stored family of edge lists. -/
noncomputable def famSet (H : PortGraph) (fam : Array (List ℕ)) : Finset (Finset (Fin H.ne)) :=
  (fam.toList.map H.toEdges).toFinset

end NearLinIsing


