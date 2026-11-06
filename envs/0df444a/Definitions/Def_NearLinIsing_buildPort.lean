-- Prove2me | Definitions.Def_NearLinIsing_buildPort
-- name    : NearLinIsing_buildPort
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:09.606499+00:00
-- url     : https://prove2.me/theorems/a6c4c537-d0f7-49ef-bf40-09df9c395a0e
-- title:
--   The charged construction of the port graph
-- statement:
--   This is the construction of $H$ as a program. It takes the 2-core by peeling vertices of degree at most one, and replaces each remaining vertex of degree $d$ by a path of $d$ ports, attaching its core edges to the ports in incidence-list order. Original edges get weight $r$ and path edges weight $1$. It then computes the nonbacktracking successors of every directed edge, the strongly connected components by Kosaraju's algorithm with explicit stacks, the vector $z$, and the rows of $P_H$ in (13). Every loop iteration is charged, so the 2-core and the components are not free. The port graph `portGraph G r` is the value of this program, which draws nothing from the tape.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, §4.1, p. 18; Eq. (13), p. 19; proof of Proposition 4.6, p. 21

import Mathlib
import Definitions.Def_NearLinIsing_Prog
import Definitions.Def_NearLinIsing_PortGraph

namespace NearLinIsing

/-!
The charged construction of the port graph `H` (§4.1, p. 18; proof of Proposition 4.6, p. 21):
2-core by peeling, ports and edges of `H`, nonbacktracking successors, strongly connected
components (Kosaraju, explicit stacks), the vector `z`, and the rows of `P_H` in (13).

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, §4.1 (p. 18), Eq. (13) (p. 19), proof of Proposition 4.6 (p. 21).

**Formalization Note.** Every loop is a `for` over a list of known length with an explicit bound
(`break` ends it early); each iteration pays a dispatch plus the listed operations (reading R2).
Reading R6: the components are computed by this charged routine, not by an uncharged `def`.
-/

/-- **2-core by peeling** (§4.1, p. 18): repeatedly delete vertices of degree zero or one. Returns
`removed` (vertex not in the 2-core) and `deg` (for core vertices, the number of core
neighbours). -/
noncomputable def peelCore (G : IncGraph) : Prog (Array Bool × Array ℕ) := do
  let n ← qN G
  let mut deg ← alloc n (0 : ℕ)
  for v in List.range n do
    tick 2 -- dispatch, write
    let d ← qDeg G v
    deg := deg.set! v d
  let mut removed ← alloc n false
  let mut queued ← alloc n false
  let mut queue : Array ℕ := #[]
  for v in List.range n do
    tick 3 -- dispatch, read, comparison
    if deg[v]! ≤ 1 then
      tick 2 -- write flag, push
      queued := queued.set! v true
      queue := queue.push v
  let mut head := 0
  for _ in List.range n do
    tick 2 -- dispatch, comparison
    if queue.size ≤ head then break
    tick 3 -- read queue cell, increment, write flag
    let x := queue[head]!
    head := head + 1
    removed := removed.set! x true
    let d ← qDeg G x
    for i in List.range d do
      tick 1 -- dispatch
      let e ← qInc G x i
      let ab ← qEnd G e
      tick 3 -- comparison, select, read flag
      let y := if ab.1 = x then ab.2 else ab.1
      if !removed[y]! then
        tick 5 -- read, decrement, write, comparison, read flag
        deg := deg.set! y (deg[y]! - 1)
        if deg[y]! ≤ 1 && !queued[y]! then
          tick 2 -- write flag, push
          queued := queued.set! y true
          queue := queue.push y
  return (removed, deg)

/-- **Ports** (§4.1, p. 18): every core vertex `v` of core degree `d` becomes `d` consecutive
ports, attached in the order of `v`'s incidence list to its core edges. Returns the port arrays
`portVert`, `portPos` (positions `1, …, d`), `portDeg`, and for every edge of `G` the port at its
first endpoint (`pAt1`) and at its second endpoint (`pAt2`). -/
noncomputable def makePorts (G : IncGraph) (removed : Array Bool) (deg : Array ℕ) :
    Prog (Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ) := do
  let n ← qN G
  let m ← qM G
  let mut np := 0
  let mut portVert : Array ℕ := #[]
  let mut portPos : Array ℕ := #[]
  let mut portDeg : Array ℕ := #[]
  let mut pAt1 ← alloc m (0 : ℕ)
  let mut pAt2 ← alloc m (0 : ℕ)
  for x in List.range n do
    tick 3 -- dispatch, read flag, branch
    if !removed[x]! then
      let d ← qDeg G x
      let mut pos := 0
      for i in List.range d do
        tick 1 -- dispatch
        let e ← qInc G x i
        let ab ← qEnd G e
        tick 3 -- comparison, select, read flag
        let y := if ab.1 = x then ab.2 else ab.1
        if !removed[y]! then
          tick 9 -- increment, three pushes, read degree, comparison, write, increment
          pos := pos + 1
          portVert := portVert.push x
          portPos := portPos.push pos
          portDeg := portDeg.push deg[x]!
          if ab.1 = x then pAt1 := pAt1.set! e np else pAt2 := pAt2.set! e np
          np := np + 1
  return (portVert, portPos, portDeg, pAt1, pAt2)

/-- **Edges of `H`** (§4.1, p. 18): the core edges of `G` between their ports, weight `r`, then the
path edges between consecutive ports of each vertex, weight `1`. Returns
`(eU, eV, wt, isOrig, gEdge)`. -/
noncomputable def makeEdges (G : IncGraph) (r : ℝ) (removed : Array Bool)
    (portPos portDeg pAt1 pAt2 : Array ℕ) :
    Prog (Array ℕ × Array ℕ × Array ℝ × Array Bool × Array ℕ) := do
  let m ← qM G
  let mut eU : Array ℕ := #[]
  let mut eV : Array ℕ := #[]
  let mut wt : Array ℝ := #[]
  let mut isOrig : Array Bool := #[]
  let mut gEdge : Array ℕ := #[]
  for e in List.range m do
    tick 1 -- dispatch
    let ab ← qEnd G e
    tick 3 -- two flag reads, conjunction
    if !removed[ab.1]! && !removed[ab.2]! then
      tick 7 -- two reads, five pushes
      eU := eU.push pAt1[e]!
      eV := eV.push pAt2[e]!
      wt := wt.push r
      isOrig := isOrig.push true
      gEdge := gEdge.push e
  tick 1 -- read the size
  for p in List.range portPos.size do
    tick 4 -- dispatch, two reads, comparison
    if portPos[p]! < portDeg[p]! then
      tick 6 -- increment, five pushes
      eU := eU.push p
      eV := eV.push (p + 1)
      wt := wt.push 1
      isOrig := isOrig.push false
      gEdge := gEdge.push m
  return (eU, eV, wt, isOrig, gEdge)

/-- **Nonbacktracking successors** (§4.1, p. 18): for the directed edge `a` with head `q` along
edge `e`, the successors are the directed edges leaving `q` along every other edge `e' ≠ e` at `q`.
Returns `(succ, pred)` over the `2 ne` directed edges. -/
noncomputable def makeSucc (np : ℕ) (eU eV : Array ℕ) : Prog (Array (List ℕ) × Array (List ℕ)) := do
  let ne ← op 1 eU.size
  let mut incH ← alloc np ([] : List ℕ)
  for e in List.range ne do
    tick 9 -- dispatch, two endpoint reads, two cell reads, two conses, two writes
    incH := incH.set! eU[e]! (e :: incH[eU[e]!]!)
    incH := incH.set! eV[e]! (e :: incH[eV[e]!]!)
  let D ← op 1 (2 * ne)
  let mut succ ← alloc D ([] : List ℕ)
  let mut pred ← alloc D ([] : List ℕ)
  for a in List.range D do
    tick 6 -- dispatch, division, parity, endpoint read, select, cell read
    let e := a / 2
    let q := if a % 2 = 0 then eV[e]! else eU[e]!
    for e' in incH[q]! do
      tick 2 -- dispatch, comparison
      if e' ≠ e then
        tick 9 -- endpoint read, comparison, arithmetic, two cell reads, two conses, two writes
        let b := if eU[e']! = q then 2 * e' else 2 * e' + 1
        succ := succ.set! a (b :: succ[a]!)
        pred := pred.set! b (a :: pred[b]!)
  return (succ, pred)

/-- **Strongly connected components** of the successor digraph by Kosaraju's algorithm with
explicit stacks: a first depth-first pass records finishing order, a second pass on the reversed
digraph in reverse finishing order labels the components. Component labels are `0, 1, …`. -/
noncomputable def kosaraju (succ pred : Array (List ℕ)) : Prog (Array ℕ) := do
  let D ← op 1 succ.size
  let mut seen ← alloc D false
  let mut order : Array ℕ := #[]
  for s in List.range D do
    tick 3 -- dispatch, read flag, branch
    if !seen[s]! then
      tick 2 -- write flag, push
      seen := seen.set! s true
      let mut stack : List (ℕ × ℕ) := [(s, 0)]
      for _ in List.range (4 * D + 4) do
        tick 2 -- dispatch, emptiness test
        match stack with
        | [] => break
        | (x, i) :: rest =>
          tick 3 -- cell read, list index, test
          match (succ[x]!)[i]? with
          | some y =>
            tick 3 -- increment, cons, flag read
            stack := (x, i + 1) :: rest
            if !seen[y]! then
              tick 2 -- write flag, push
              seen := seen.set! y true
              stack := (y, 0) :: stack
          | none =>
            tick 2 -- push, pop
            order := order.push x
            stack := rest
  let mut comp ← alloc D D
  let mut nc := 0
  for k in List.range D do
    tick 5 -- dispatch, index arithmetic, read, read label, comparison
    let s := order[D - 1 - k]!
    if comp[s]! = D then
      tick 2 -- write label, push
      comp := comp.set! s nc
      let mut stack : List ℕ := [s]
      for _ in List.range (4 * D + 4) do
        tick 2 -- dispatch, emptiness test
        match stack with
        | [] => break
        | x :: rest =>
          tick 2 -- pop, cell read
          stack := rest
          for y in pred[x]! do
            tick 3 -- dispatch, read label, comparison
            if comp[y]! = D then
              tick 2 -- write label, push
              comp := comp.set! y nc
              stack := y :: stack
      tick 1 -- increment
      nc := nc + 1
  return comp

/-- **The vector `z` and the rows of `P_H`** (§4.1, p. 18; Eq. (13), p. 19): `z_a = 1` on original
directed edges and `r` times the number of ports ahead on directed path edges; the row of `a` lists
`(b, t_{e(b)} z_b / z_a)` for the successors `b` of `a` in the component of `a`. -/
noncomputable def makeRows (r : ℝ) (eU eV : Array ℕ) (wt : Array ℝ) (isOrig : Array Bool)
    (portPos portDeg : Array ℕ) (succ : Array (List ℕ)) (comp : Array ℕ) :
    Prog (Array ℝ × Array (List (ℕ × ℝ))) := do
  let D ← op 2 (2 * eU.size) -- size read, multiplication
  let mut z ← alloc D (0 : ℝ)
  for a in List.range D do
    tick 14 -- dispatch, division, parity, two endpoint reads, flag read, two position reads,
            -- comparison, degree read, two arithmetic, multiplication, write
    let e := a / 2
    let p := if a % 2 = 0 then eU[e]! else eV[e]!
    let q := if a % 2 = 0 then eV[e]! else eU[e]!
    let za : ℝ :=
      if isOrig[e]! then 1
      else if portPos[p]! < portPos[q]! then r * ((portDeg[q]! : ℝ) - portPos[q]! + 1)
      else r * (portPos[q]! : ℝ)
    z := z.set! a za
  let mut rowP ← alloc D ([] : List (ℕ × ℝ))
  for a in List.range D do
    tick 2 -- dispatch, cell read
    for b in succ[a]! do
      tick 4 -- dispatch, two label reads, comparison
      if comp[b]! = comp[a]! then
        tick 8 -- division, weight read, two z reads, multiplication, division, cons, write
        rowP := rowP.set! a ((b, wt[b / 2]! * z[b]! / z[a]!) :: rowP[a]!)
  return (z, rowP)

/-- **The port-graph construction** (§4.1, p. 18; proof of Proposition 4.6, p. 21), charged: the
2-core, the ports, the edges of `H`, the successors, the components, `z` and `P_H`. -/
noncomputable def buildPort (G : IncGraph) (r : ℝ) : Prog PortGraph := do
  let (removed, deg) ← peelCore G
  let (portVert, portPos, portDeg, pAt1, pAt2) ← makePorts G removed deg
  let (eU, eV, wt, isOrig, gEdge) ← makeEdges G r removed portPos portDeg pAt1 pAt2
  tick 1 -- read the size
  let (succ, pred) ← makeSucc portPos.size eU eV
  let comp ← kosaraju succ pred
  let (z, rowP) ← makeRows r eU eV wt isOrig portPos portDeg succ comp
  tick 2 -- two size reads
  return { np := portPos.size, ne := eU.size, eU := eU, eV := eV, wt := wt, isOrig := isOrig,
           gEdge := gEdge, portVert := portVert, portPos := portPos, portDeg := portDeg,
           succ := succ, scc := comp, z := z, rowP := rowP }

/-- **The port graph `H` of `G` with flow weight `r`** (§4.1, p. 18): the output of `buildPort`,
which draws nothing from the tape, so any tape gives the same value. -/
noncomputable def portGraph (G : IncGraph) (r : ℝ) : PortGraph := runVal (buildPort G r) (fun _ => 0)

end NearLinIsing


