-- Prove2me | Definitions.Def_TwMSOCount_Main_Types
-- name    : TwMSOCount_Main_Types
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:47:05.266617+00:00
-- url     : https://prove2.me/theorems/f968064d-cbb7-4c85-81eb-972d85d853de
-- title:
--   Rank-q MSO2 types, codes of finite boundaried graphs, construction terms, and the graphs used by the recurrences
-- statement:
--   The **rank-$q$ type** of a colored $B$-boundaried graph $H$ (Definition C.2) is the set of MSO2 sentences over $V_{C,B}$ (constants among $\{c_b : b\in B\}$, interpreted by $\iota_B$) of quantifier rank at most $q$ that hold in $I(H,\chi,\iota_B)$; two graphs are $q$-equivalent when their types are equal.
--
--   A **finite graph code** is a tuple $(N, \text{edges}, \text{colors}, \text{labels})$: vertices $0,\dots,N-1$, a list of edges, the list of vertex colors (read modulo $r$), and a list of (label, vertex) pairs; the decoded graph has the listed labels with their least listed vertex. Every finite boundaried graph has a code (through an enumeration of its vertices). Label sets are coded by the increasing list of their indices.
--
--   **Construction terms** (Definition C.5): the empty-graph symbol; a unary operation of Table 2 (introduce, forget, relabel, AddEdge) applied to a term; the gluing of two terms. The value of a term is computed recursively and is undefined when some operation is undefined.
--
--   The **graphs used by the recurrences** (Proposition 5.1) are the well-formed graphs of treewidth at most $k$ with at most $6(k+1)$ boundary labels, the graphs on at most $6(k+1)$ boundary vertices alone, the collections of valid contexts, and the candidate parents built from a collection with all inherited labels by adding a local edge pattern, before or after forgetting $N$. The **tests** read by the recurrences are coded by a kind and label lists: $\mathrm{Width}_k$, $\mathrm{NoEdge}_Q$, $\mathrm{Piece}_Q$, $\Phi_{B,B_S,N}$, $\psi$, a boundary color, a boundary adjacency.
--
--   `UsedGraph` uses structural `BoundaryWF`; arbitrary output-label values do not affect states or construction terms.
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Appendix C.3–C.6, pp. 27–31 (PDF 28–32), Definitions C.2, C.5, C.7, Table 2

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator
import Definitions.Def_TwMSOCount_Main_Tables

namespace TwMSOCount.Main

open Classical

variable {r k : ℕ}

/-- The rank-`q` MSO2 type `tp^{MSO}_{q,B}(I(H, χ, ι_B))` (Definition C.2): the set of sentences
over `V_{C,B}` (constants among the labels of `B`) of quantifier rank at most `q` that hold in the
boundaried incidence structure of `H`. -/
def tp (q : ℕ) (H : BGraph r k) : Set (Formula r (Lab k)) :=
  {φ | φ.IsSentence ∧ φ.consts ⊆ H.B ∧ φ.qr ≤ q ∧ H.Models φ}

/-- Code of a finite colored boundaried graph: number of vertices `N` (vertices `0, …, N-1`), a list
of edges `(i, j)`, the list of vertex colors, and a list of (label, vertex) pairs. -/
abbrev GCode := ℕ × List (ℕ × ℕ) × List ℕ × List (ℕ × ℕ)

/-- Code of a label set: its labels' indices in increasing order. -/
noncomputable def labCode (B : Finset (Lab k)) : List ℕ := (B.sort (· ≤ ·)).map Fin.val

/-- The label set with the indices of a list. -/
noncomputable def labDecode (k : ℕ) (l : List ℕ) : Finset (Lab k) :=
  Finset.univ.filter (fun b => b.val ∈ l)

/-- The boundaried graph of a code: vertices `Fin N`, `i ~ j` when `(i, j)` or `(j, i)` is listed
(`i ≠ j`), color of `i` the `i`-th listed color mod `r`, labels `b ∈ Λ_k` listed with some vertex
`< N`, `ι(b)` the least such vertex, output label of `i` equal to `i`. -/
noncomputable def decodeG (r k : ℕ) [NeZero r] (x : GCode) : BGraph r k where
  V := Fin x.1
  G := SimpleGraph.fromRel (fun i j => (i.val, j.val) ∈ x.2.1)
  col := fun i => ⟨x.2.2.1.getD i.val 0 % r, Nat.mod_lt _ (NeZero.pos r)⟩
  B := Finset.univ.filter (fun b : Lab k => ∃ v, v < x.1 ∧ (b.val, v) ∈ x.2.2.2)
  ι := fun b => ⟨Nat.find (Finset.mem_filter.mp b.2).2, (Nat.find_spec (Finset.mem_filter.mp b.2).2).1⟩
  out := fun i => i.val

/-- A code of an abstract finite boundaried graph, through an enumeration of its vertices. -/
noncomputable def encodeG (H : BGraph r k) : GCode :=
  let e := Fintype.equivFin H.V
  (Fintype.card H.V,
    ((Finset.univ : Finset (Fin (Fintype.card H.V) × Fin (Fintype.card H.V))).filter
      (fun p => H.G.Adj (e.symm p.1) (e.symm p.2))).toList.map (fun p => (p.1.val, p.2.val)),
    (List.finRange (Fintype.card H.V)).map (fun i => (H.col (e.symm i)).val),
    H.B.attach.toList.map (fun b => (b.1.val, (e (H.ι b)).val)))

/-- The empty graph with empty boundary. -/
def emptyBGraph (r k : ℕ) : BGraph r k where
  V := Empty
  G := ⊥
  col := fun v => v.elim
  B := ∅
  ι := fun x => absurd x.2 (Finset.notMem_empty x.1)
  out := fun v => v.elim

/-- Construction terms (Definition C.5): the empty-graph symbol, a unary operation of Table 2
applied to a term, or the gluing of two terms. -/
inductive CTerm (r k : ℕ) where
  | empty : CTerm r k
  | introduce : Lab k → Fin r → CTerm r k → CTerm r k
  | forget : Lab k → CTerm r k → CTerm r k
  | relabel : (Lab k → Lab k) → CTerm r k → CTerm r k
  | addEdge : Lab k → Lab k → CTerm r k → CTerm r k
  | glue : CTerm r k → CTerm r k → CTerm r k

/-- The value of a construction term, `none` when some operation is undefined. -/
noncomputable def CTerm.value : CTerm r k → Option (BGraph r k)
  | .empty => some (emptyBGraph r k)
  | .introduce b c t => t.value.bind (fun H => if b ∉ H.B then some (H.introduce b c) else none)
  | .forget b t => t.value.bind (fun H => if b ∈ H.B then some (H.forget b) else none)
  | .relabel π t => t.value.bind (fun H => if Set.InjOn π ↑H.B then some (H.relabel π) else none)
  | .addEdge a b t => t.value.bind (fun H =>
      if H.AddEdgeOK a b then some (H.addEdges {s(a, b)}) else none)
  | .glue t₁ t₂ => t₁.value.bind (fun H₁ => t₂.value.bind (fun H₂ =>
      if BGraph.GlueOK H₁ H₂ then some (BGraph.glue H₁ H₂) else none))

/-- The graphs used by the recurrences (Proposition 5.1): well-formed graphs of treewidth at most
`k` with at most `6(k+1)` boundary labels; graphs on at most `6(k+1)` boundary vertices alone;
collections of a valid context; and candidate parents (a collection with all inherited labels
`B \ B_S`, with a local edge pattern `F ⊆ (J choose 2)` added, before or after forgetting `N`). -/
def UsedGraph [NeZero r] (H : BGraph r k) : Prop :=
  H.BoundaryWF ∧
  ((H.B.card ≤ 6 * (k + 1) ∧ H.tw ≤ k) ∨
   (H.B.card ≤ 6 * (k + 1) ∧ H.int = ∅) ∨
   (∃ (γ : Ctx r k) (I : Finset (Lab k)), γ.Valid ∧ I ⊆ γ.B \ γ.BS ∧ IsCollection γ I H) ∨
   (∃ (γ : Ctx r k) (K : BGraph r k) (F : Finset (Sym2 (Lab k))), γ.Valid ∧
      IsCollection γ (γ.B \ γ.BS) K ∧ F ∈ (pairs γ.J).powerset ∧ K.AddEdgesOK F ∧
      (BGraph.IsoBL H (K.addEdges F) ∨ BGraph.IsoBL H ((K.addEdges F).forgetSet γ.N))))

/-- The tests read by the recurrences, coded as `(kind, l₁, l₂, l₃)`: `0` `Width_k`; `1`
`NoEdge_Q` with `Q = l₁`; `2` `Piece_Q` with `Q = l₁`; `3` `Φ_{B,B_S,N}` with `B, B_S, N =
l₁, l₂, l₃`; `4` the sentence `ψ` (on graphs with empty boundary); `5` boundary color: `l₁ = [b, c]`
means `χ(ι(b)) = c`; `6` boundary adjacency: `l₁ = [a, b]` means `ι(a) ~ ι(b)`. -/
def testSem [NeZero r] (ψ : Formula r Empty) (t : ℕ × List ℕ × List ℕ × List ℕ)
    (H : BGraph r k) : Prop :=
  match t.1 with
  | 0 => H.tw ≤ k
  | 1 => NoEdgeT H (labDecode k t.2.1)
  | 2 => PieceT H (labDecode k t.2.1)
  | 3 => PhiT (labDecode k t.2.1) (labDecode k t.2.2.1) (labDecode k t.2.2.2) H
  | 4 => H.B = ∅ ∧ ModelsPsi H.G H.col ψ
  | 5 => ∃ (b : Lab k) (h : b ∈ H.B), b.val = t.2.1.getD 0 0 ∧
      (H.col (H.ι ⟨b, h⟩)).val = t.2.1.getD 1 0
  | 6 => ∃ (a b : Lab k) (ha : a ∈ H.B) (hb : b ∈ H.B), a.val = t.2.1.getD 0 0 ∧
      b.val = t.2.1.getD 1 0 ∧ H.G.Adj (H.ι ⟨a, ha⟩) (H.ι ⟨b, hb⟩)
  | _ => False

end TwMSOCount.Main


