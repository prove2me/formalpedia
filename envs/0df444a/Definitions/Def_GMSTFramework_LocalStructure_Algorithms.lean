-- Prove2me | Definitions.Def_GMSTFramework_LocalStructure_Algorithms
-- name    : GMSTFramework_LocalStructure_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:03:21.567685+00:00
-- url     : https://prove2.me/theorems/ce9d5db1-f613-46a5-b061-247b8e6f57cd
-- title:
--   Oracle algorithms, the colour-explorer oracle, input encodings and output certificates (machine model for Prop. 6.1, Thm. 6.4, Props. 7.5–7.8, Thm. 8.2)
-- statement:
--   The algorithmic clauses are stated for programs of the published deterministic RAM with an oracle (`CapacitatedKMedianFPT.Main`): an algorithm halts on the encoded input with the encoded output in the final memory (cell 0 the length, then the entries), within a bound on the **word-RAM time** (each step costs one per input word of its operands, for the transdichotomous word length of the input) and a bound on the number of **oracle calls** counted separately. As on p. 26, the time counts preparing queries and reading answers but not the oracle's computation. The oracle of a colour-explorer $\varphi$ answers the encoding of a boundaried graph $X$ with the bit mask $\sum_{i\in\varphi(X)}2^i$.
--
--   Inputs and outputs are lists of natural numbers: graphs as $|V(G)|$, their edges by labels and the colour list of every vertex; paths and cycles as label sequences; meshes by their paths; renditions by one record per cell (vertices and edges of $\sigma(c)$, nodes $\pi(N(c))$); extended surface-walls by their segment kinds, their subdivision paths (indexed by elementary edges) and their hyperedge ends; minor-models by their branch sets.
--
--   **Formalization Note.** `Describes…` are relations between objects and certificates (a rendition's cells may be listed in any order, a cycle from any start in either direction), so an algorithm must handle every description of its input, and its output must describe a valid object. `BigO C f := C·(f+1)` is used only where the printed bound can be 0.
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), p. 26 (PDF 29) "Oracle access to colour-explorers"; algorithmic clauses p. 48, 51, 60–61, 85 (PDF 51, 54, 63–64, 88)

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Machine
import Definitions.Def_GMSTFramework_LocalStructure_Societies
import Definitions.Def_GMSTFramework_LocalStructure_ColourExplorers

open scoped Classical

noncomputable section

namespace GMSTFramework.LocalStructure

open CapacitatedKMedianFPT.Main

/-!
# Oracle algorithms, input encodings and output certificates

Gorsky, Protopapas, Wiederrecht, *A unifying framework for Graph Minor Structure Theorems with
polynomial bounds*, STOC 2027 submission (manuscript sha256 b2ee466d…), "Oracle access to
colour-explorers" p. 26 (PDF 29), and the algorithmic clauses of Proposition 6.1, Theorem 6.4,
Propositions 7.5, 7.6, 7.8 and Theorem 8.2.

**Machine model.** The published deterministic RAM of `CapacitatedKMedianFPT.Main` (programs over
rational cells with an oracle-query instruction; `RunsTo`, `Stats.wordTime`, `Stats.queries`).
Running time is the transdichotomous word-RAM time `wordTime` with the word length of the input
(`wordSizeOf`); the cost of a query (reading its argument cells and writing the answer) is counted,
the oracle's own computation is not, and the oracle calls are counted separately (`queries`), as
on p. 26. The output is read from the final memory: cell `0` holds its length `L`, cells
`1, …, L` its entries.

**Colour-explorer oracle.** `explorerOracle φ` answers the query `encBGraph X` (a valid boundaried
graph) with the bit mask `∑_{i ∈ φ(X)} 2^i`, and every other query with `0`.

**Encodings.** Lists of natural numbers are self-delimiting (`encNats`: length, then entries);
nested lists likewise (`encNested`); a tuple is the concatenation of its encoded parts. Vertices
are named by their labels (`vName`). A graph is encoded as `|V(G)|`, its edges `[u, w]` (`u < w`,
by increasing `u`, then `w`), and the colour list of every vertex `1, …, |V(G)|`; a path by the names
along it; a cycle by the names along a closed walk around it (any start, either direction); a
mesh by its horizontal then vertical paths; a rendition by one record per cell (the names of
`V(σ(c))`, its edges, and `π(N(c))`, each sorted), cells in any order; an extended surface-wall by
its order, its segment kinds (`0` wall, `1` handle, `2` crosscap, `3` vortex, `4 + q` flap of arity
`q`), one record `[idx x, idx y] ++ path` for every elementary edge `xy` with `idx x < idx y`
(`idx` the lexicographic index of `(segment, copy, row, column)`), and the hyperedge ends of every
segment. These are relations ("the list describes the object"), so an algorithm must work for every
description of its input and its output must describe a valid object.
-/

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Running an algorithm -/

/-- The output list of a final memory: cell `0` holds the length, cells `1, 2, …` the entries. -/
def outputOf (m : Memory) : List ℚ := (List.range (⌊m 0⌋.toNat)).map fun i => m (i + 1)

/-- The program `P` with oracle `O` halts on `input` with output `out` within word-RAM time `time`
and at most `queries` oracle calls. -/
def RunsWithin (P : Program) (O : Oracle) (input out : List ℚ) (time queries : ℕ) : Prop :=
  ∃ (m : Memory) (s : Stats), RunsTo P O input m s ∧ outputOf m = out ∧
    s.wordTime (wordSizeOf input) ≤ time ∧ s.queries ≤ queries

/-! ### Encodings -/

/-- A self-delimiting list of natural numbers. -/
def encNats (l : List ℕ) : List ℚ := (l.length : ℚ) :: l.map fun x => (x : ℚ)

/-- A self-delimiting list of lists of natural numbers. -/
def encNested (ls : List (List ℕ)) : List ℚ := (ls.length : ℚ) :: ls.flatMap encNats

/-- The sorted list of the elements of a finite set of naturals. -/
def sortedNats (s : Finset ℕ) : List ℕ := s.sort (· ≤ ·)

/-- The boundaried graph as a query: vertices, edges, colours of the vertices (in increasing order),
boundary in the order `ρ`, and the distinguished set. -/
def encBGraph (X : BGraph) : List ℚ :=
  encNats (sortedNats X.V) ++
    encNested ((sortedNats X.V).flatMap fun u => (sortedNats X.V).filterMap fun w =>
      if u < w ∧ X.adj.Adj u w then some [u, w] else none) ++
    encNested ((sortedNats X.V).map fun v => sortedNats (X.ψ v)) ++
    encNats X.ord ++ encNats (sortedNats X.A)

/-- The bit mask `∑_{i ∈ S} 2^i`. -/
def bitMask (S : Finset ℕ) : ℚ := ∑ i ∈ S, (2 : ℚ) ^ i

/-- The oracle of a colour-explorer: a query encoding a valid boundaried graph `X` is answered by
the bit mask of `φ(X)`, any other query by `0`. -/
def explorerOracle (φ : BGraph → Finset ℕ) : Oracle := fun args =>
  if h : ∃ X : BGraph, X.Valid ∧ encBGraph X = args then bitMask (φ (Classical.choose h)) else 0

/-- The names of the vertices of a set, sorted. -/
def namesOf (label : V ≃ Fin (Fintype.card V)) (S : Set V) : List ℕ :=
  sortedNats ((Finset.univ.filter fun v => v ∈ S).image (vName label))

/-- The edges `[u, w]` (`u < w`) between names of the edge set `E`, by increasing `u`, then `w`. -/
def edgeCode (label : V ≃ Fin (Fintype.card V)) (E : Set (Sym2 V)) : List (List ℕ) :=
  (List.range (Fintype.card V + 1)).flatMap fun u => (List.range (Fintype.card V + 1)).filterMap
    fun w => if u < w ∧ ∃ x y, vName label x = u ∧ vName label y = w ∧ s(x, y) ∈ E then some [u, w]
      else none

/-- The encoding of the labelled colorful graph `(G, χ)`. -/
def encGraph (G : SimpleGraph V) (χ : V → Finset ℕ) (label : V ≃ Fin (Fintype.card V)) :
    List ℚ :=
  encNats [Fintype.card V] ++ encNested (edgeCode label G.edgeSet) ++
    encNested (List.ofFn fun i : Fin (Fintype.card V) => sortedNats (χ (label.symm i)))

/-- The names along a path. -/
def pathNames (label : V ≃ Fin (Fintype.card V)) (P : GPath G) : List ℕ :=
  P.walk.support.map (vName label)

/-- `l` describes the cycle `C`: the names along a closed walk around `C` (without repeating the
start). -/
def DescribesCycle (label : V ≃ Fin (Fintype.card V)) (C : G.Subgraph) (l : List ℕ) : Prop :=
  ∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ w.toSubgraph = C ∧ w.support.tail.map (vName label) = l

/-- The encoding of a mesh: its horizontal, then its vertical paths. -/
def encMesh (label : V ≃ Fin (Fintype.card V)) {n m : ℕ} (M : Mesh G n m) : List ℚ :=
  encNested (List.ofFn fun i => pathNames label (M.P i)) ++
    encNested (List.ofFn fun j => pathNames label (M.Q j))

/-- The encoding of a linkage: the names along its paths. -/
def encLinkage (label : V ≃ Fin (Fintype.card V)) {n : ℕ} (L : Linkage G n) : List ℚ :=
  encNested (List.ofFn fun i => pathNames label (L.path i))

/-- The record of a cell: `|V(σ(c))|`, the names of `V(σ(c))`, the number of edges, the edges
flattened, `|N(c)|`, the names of `π(N(c))`. -/
def cellRecord (label : V ≃ Fin (Fintype.card V)) (S : G.Subgraph) (nodes : Set V) : List ℕ :=
  let vs := namesOf label S.verts
  let es := edgeCode label S.edgeSet
  let ns := namesOf label nodes
  vs.length :: vs ++ (es.length :: es.flatten) ++ (ns.length :: ns)

/-- `cells` describes the rendition `ρ`: one record per cell, in some order. -/
def DescribesRendition {X : Type} [TopologicalSpace X] (label : V ≃ Fin (Fintype.card V))
    {H : G.Subgraph} (ρ : Rendition X H) (cells : List (List ℕ)) : Prop :=
  ∃ f : Fin cells.length → Set X, Function.Injective f ∧ Set.range f = ρ.cells ∧
    ∀ i, cells.get i = cellRecord label (ρ.σ (f i)) (ρ.cellNodeVerts (f i))

/-- The code of a segment kind. -/
def SegKind.code : SegKind → ℕ
  | .wall => 0
  | .handle => 1
  | .crosscap => 2
  | .vortex => 3
  | .flap q => 4 + q

/-- The lexicographic index of an elementary vertex. -/
def EVert.idx {ℓ n : ℕ} (x : EVert ℓ n) : ℕ :=
  ((x.seg.val * 2 + x.copy.val) * n + x.row.val) * (8 * n) + x.col.val

/-- `(ks, es, zl)` describes the extended surface-wall `D`. -/
def DescribesWall (label : V ≃ Fin (Fintype.card V)) {n : ℕ} (D : SurfaceWall G n)
    (ks : List ℕ) (es zl : List (List ℕ)) : Prop :=
  ks = D.kinds.map SegKind.code ∧
  (∀ x y, EAdj D.kinds n x y → x.idx < y.idx → [x.idx, y.idx] ++ pathNames label (D.pth x y) ∈ es) ∧
  (∀ e ∈ es, ∃ x y, EAdj D.kinds n x y ∧ x.idx < y.idx ∧
    e = [x.idx, y.idx] ++ pathNames label (D.pth x y)) ∧
  es.Nodup ∧ zl = List.ofFn fun i => namesOf label (D.zs i : Set V)

/-- The encoding of a surface-wall description. -/
def encWall (n : ℕ) (ks : List ℕ) (es zl : List (List ℕ)) : List ℚ :=
  encNats [n] ++ encNats ks ++ encNested es ++ encNested zl

/-- `bs` describes the minor-model `μ`: the names of its branch sets, sorted. -/
def DescribesModel {W : Type} [Fintype W] {H : SimpleGraph W} (label : V ≃ Fin (Fintype.card V))
    (e : W ≃ Fin (Fintype.card W)) (μ : H.Minor G) (bs : List (List ℕ)) : Prop :=
  bs = List.ofFn fun i => namesOf label (μ.branchSet (e.symm i))

/-- The time bound `O(f)`: at most `C · (f + 1)` (an algorithm always takes a step). -/
def BigO (C f : ℕ) : ℕ := C * (f + 1)

end GMSTFramework.LocalStructure


