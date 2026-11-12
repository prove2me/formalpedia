-- Prove2me | Definitions.Def_BunkbedTransfer
-- name    : BunkbedTransfer
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-12T15:18:30.569445+00:00
-- url     : https://prove2.me/theorems/01c543ed-e6ae-480f-9cc6-1a1658fdafc1
-- title:
--   Transfer matrix for Hollom's hypergraph
-- statement:
--   The Wierman--Ziff connection probability on Hollom's $3$-uniform hypergraph is a sum over $5^{12}$ state configurations, which cannot be enumerated directly. This file sets up a transfer matrix that evaluates it in six steps.
--
--   Hollom's six hyperedges can be listed along the path $\rho = (u_1, u_3, u_6, u_5, u_4, u_8, u_{10})$ of Eq. [5], written here as $0 \to 2 \to 5 \to 4 \to 3 \to 7 \to 9$, in such a way that **every intermediate path vertex lies in exactly two consecutive hyperedges**. Sweeping the hyperedges in that order therefore only ever needs to remember the partition induced on the five *special* vertices — the two endpoints $0$ and $9$ of the connection event, and the transversal set $T = \{1, 6, 8\}$ over which the posts stand — together with the path vertex currently being carried. That is five slots, and `step` is one sweep of one hyperedge: it opens a slot for the incoming path vertex, merges the slots that the hyperedge's Wierman--Ziff state joins, and then forgets the spent path vertex.
--
--   A state is recorded as the vector sending each slot to the least slot in its block; `Represents r R` says that such a vector names the partition $R$, and `levelRel` is the partition that one level of a configuration induces on the five special vertices.
--
--   The file also gives the glued connectivity in closed form. The two levels of the bunkbed interact only through the posts over $T$, so connectivity is governed by the set $A$ of posts reachable from vertex $0$ on level $0$: $A$ starts as the posts lying in $0$'s level-$0$ block and is closed under the blocks of *either* level, three rounds sufficing because there are only three posts. Then $0@0 \leftrightarrow 9@0$ iff $0 \sim_0 9$ or some $t \in A$ has $t \sim_0 9$, and $0@0 \leftrightarrow 9@1$ iff some $t \in A$ has $t \sim_1 9$. Writing the answer this way makes visible that the level-$1$ profile enters only through its restriction to $\{1, 6, 8, 9\}$.
-- source:
--   Gladkov, Pak, Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) no. 24, e2420725122; Section 3, Hollom's 3-uniform hypergraph (Fig. 1) and the path $\rho$ of Eq. [5].

import Definitions.Def_BunkbedHypergraph

/-!
# The transfer matrix for Hollom's hypergraph

Section 3 of Gladkov–Pak–Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) e2420725122.

`wzProb` is a sum over `5 ^ 12` state configurations, which cannot be enumerated. The six
hyperedges of Hollom's hypergraph are however arranged along the path `ρ` of Eq. [5],
`0 → 2 → 5 → 4 → 3 → 7 → 9`, in such a way that **every intermediate path vertex lies in
exactly two consecutive hyperedges**. Processing the hyperedges in that order therefore only
ever needs to remember the partition induced on the five *special* vertices

* `0` and `9`, the two endpoints of the connection event, and
* `1, 6, 8`, the transversal set `T` over which the posts stand,

together with the current path vertex — five slots in all. That is the transfer-matrix state
space, and it has only `47` reachable values after all six hyperedges.

Slots `0,1,2,3,4` stand for the vertices `0, 1, 6, 8, cur`, where `cur` is the path vertex
currently being carried; it is `0` before any hyperedge is processed and `9` after all six.
A state is recorded as the vector of *block representatives*, each slot mapped to the least
slot lying in the same block.
-/

namespace Bunkbed.TM

open Bunkbed Bunkbed.Hyper Finset

/-- A transfer-matrix state: the partition of the five tracked slots, as the vector sending
each slot to the least slot in its block. -/
abbrev St := Fin 5 → Fin 5

/-- During one transfer step six slots are live: slot `4` still carries the outgoing path
vertex while slot `5` carries the incoming one. -/
abbrev St6 := Fin 6 → Fin 6

/-- The five special vertices of Hollom's hypergraph, in slot order. -/
def sp : Fin 5 → Fin 10 := ![0, 1, 6, 8, 9]

/-- The path `ρ` of Eq. [5]: the seven path vertices in order. -/
def pathV : Fin 7 → Fin 10 := ![0, 2, 5, 4, 3, 7, 9]

/-- Slot of the transversal vertex of hyperedge `i`; the transversal vertices are
`1, 8, 6, 1, 6, 8`, lying in slots `1, 3, 2, 1, 2, 3`. -/
def trSlot : Fin 6 → Fin 6 := ![1, 3, 2, 1, 2, 3]

/-- Where the three positions `(a, b, c)` of hyperedge `i` sit among the six live slots:
the transversal vertex, the outgoing path vertex, the incoming path vertex. -/
def triplePos (i : Fin 6) : Fin 3 → Fin 6 := ![trSlot i, 4, 5]

/-- Which positions of its hyperedge a WZ state joins. -/
def wzPairs : WZ → List (Fin 3 × Fin 3)
  | .abc   => [(0, 1), (1, 2), (0, 2)]
  | .ab_c  => [(0, 1)]
  | .ac_b  => [(0, 2)]
  | .a_bc  => [(1, 2)]
  | .a_b_c => []

/-- Merge the blocks of slots `i` and `j`, keeping "representative = least slot in block". -/
def uni6 (s : St6) (i j : Fin 6) : St6 :=
  fun k => if s k = max (s i) (s j) then min (s i) (s j) else s k

/-- Open slot `5` for the incoming path vertex, as its own block. -/
def embed5 (r : St) : St6 :=
  fun k => if h : k.val < 5 then (r ⟨k.val, h⟩).castSucc else 5

/-- The five slots that survive a transfer step: the four special ones, and slot `5`, which
becomes the new `cur`. -/
def newSlot : Fin 5 → Fin 6 := ![0, 1, 2, 3, 5]

/-- One transfer step: open a slot for the incoming path vertex, apply the merges dictated by
the WZ state of hyperedge `i`, then forget the spent path vertex and recanonicalise. -/
def step (i : Fin 6) (t : WZ) (r : St) : St :=
  let s : St6 :=
    (wzPairs t).foldl (fun acc pq => uni6 acc (triplePos i pq.1) (triplePos i pq.2)) (embed5 r)
  fun a => (List.finRange 5).foldl
    (fun acc b => if s (newSlot b) = s (newSlot a) then min acc b else acc) 4

/-- The state before any hyperedge is processed: `cur = 0`, so slot `4` sits in slot `0`'s
block and the three transversal slots are singletons. -/
def stInit : St := ![0, 1, 2, 3, 0]

/-- Fold the first `k` hyperedges of a level configuration into a transfer-matrix state. -/
def fold : (k : ℕ) → (k ≤ 6) → (Fin 6 → WZ) → St
  | 0, _, _ => stInit
  | k + 1, h, c => step ⟨k, by omega⟩ (c ⟨k, by omega⟩) (fold k (by omega) c)

/-- The profile of a level configuration: the partition it induces on `{0, 1, 6, 8, 9}`. -/
def prof (c : Fin 6 → WZ) : St := fold 6 le_rfl c


/-! ## The graph-theoretic side

`St` is a *representation* of a partition; the predicate `Represents` says that a state vector
names exactly the partition induced by one level of a WZ configuration. Stating the transfer
matrix through `Represents` avoids having to reason about canonical representatives.
-/

/-- The edges one level of a WZ configuration contributes. -/
def levelEdges (c : Fin 6 → WZ) (l : Fin 2) : Finset (Sym2 (Fin 10 × Fin 2)) :=
  Finset.univ.biUnion (fun i : Fin 6 => (c i).edges (hollomTriple i) l)

/-- The partition that one level induces on the five special vertices. -/
def levelRel (c : Fin 6 → WZ) (l : Fin 2) : Fin 5 → Fin 5 → Prop :=
  fun a b => (ofEdges (levelEdges c l)).Reachable (sp a, l) (sp b, l)

/-- `r` names the partition `R`. -/
def Represents (r : St) (R : Fin 5 → Fin 5 → Prop) : Prop := ∀ a b, r a = r b ↔ R a b

/-! ## Glued connectivity in closed form

Levels interact only through the posts over `T = {1, 6, 8}`, which occupy slots `1, 2, 3`.
So connectivity is governed by the set `A` of posts reachable from vertex `0` on level `0`:
`A` starts as the posts lying in `0`'s level-`0` block and is closed under the blocks of
*either* level. Three rounds suffice, there being only three posts. Writing the answer this
way makes it visible that the level-`1` profile enters only through its restriction to
`{1, 6, 8, 9}` — which is what collapses the final double sum from `47 × 47` to `47 × 15`.
-/

/-- The slots carrying the transversal set `T = {1, 6, 8}`. -/
def postSlots : List (Fin 5) := [1, 2, 3]

/-- One round of post closure. -/
def closeStep (r0 r1 : St) (A : Fin 5 → Bool) : Fin 5 → Bool :=
  fun t => A t || postSlots.any (fun s => A s && (r0 s = r0 t || r1 s = r1 t))

/-- The posts reachable from vertex `0` sitting on level `0`. -/
def postSet (r0 r1 : St) : Fin 5 → Bool :=
  (closeStep r0 r1)^[3] (fun t => postSlots.contains t && (r0 0 = r0 t))

/-- `0` on level `0` is connected to `9` on level `l`. -/
def glueConn (r0 r1 : St) (l : Fin 2) : Bool :=
  if l = 0 then (r0 0 = r0 4) || postSlots.any (fun t => postSet r0 r1 t && (r0 t = r0 4))
  else postSlots.any (fun t => postSet r0 r1 t && (r1 t = r1 4))

end Bunkbed.TM


