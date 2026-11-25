-- Prove2me | Definitions.Def_DetDLP_D4CoreCut
-- name    : DetDLP_D4CoreCut
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:36:49.269393+00:00
-- url     : https://prove2.me/theorems/2c45d5d6-4fb2-4dcf-9ca5-9c9b9b55bab9
-- title:
--   Canonical core deletion and lookup reattachment
-- statement:
--   Increasing vertex and edge index lists implement deletion of an independent lookup set, its boundary hosts, port inclusions, pin positions, and reattachment to explicitly indexed leaves. The input promise supplies independence. The raw bit interface represents an arbitrary leaf count in unary so that even isolated leaves can be emitted.

import Definitions.Def_DetDLP_D4Plan
import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_ToTuring_Lib_List2
set_option autoImplicit false
namespace DetDLP.D4CoreCut
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev Graph := BipartiteMultigraph
abbrev Word := List Bool
variable (G : Graph) (L : Finset (Fin G.nV))
def coreVerts := (List.finRange G.nV).filter (fun v => decide (v ∉ L))
def lookupVerts := (List.finRange G.nV).filter (fun v => decide (v ∈ L))
def coreEdges := (List.finRange G.nE).filter (fun e => decide ((G.endpoints e).1 ∉ L ∧ (G.endpoints e).2 ∉ L))
def boundaryEdges := (List.finRange G.nE).filter (fun e => decide ((G.endpoints e).1 ∈ L ∨ (G.endpoints e).2 ∈ L))
abbrev V := Fin (coreVerts G L).length
abbrev E := Fin (coreEdges G L).length
abbrev B := Fin (boundaryEdges G L).length

def idx {α : Type} [DecidableEq α] (xs : List α) (x : α) (h : x ∈ xs) : Fin xs.length :=
  ⟨xs.idxOf x, List.idxOf_lt_length_iff.mpr h⟩
@[simp] theorem get_idx {α : Type} [DecidableEq α] (xs : List α) (x : α) (h : x ∈ xs) : xs.get (idx xs x h) = x :=
  List.getElem_idxOf _

def origV (v : V G L) := (coreVerts G L).get v
def origE (i : E G L) := (coreEdges G L).get i
def origB (i : B G L) := (boundaryEdges G L).get i

theorem internal_ok (i : E G L) : (G.endpoints (origE G L i)).1 ∉ L ∧ (G.endpoints (origE G L i)).2 ∉ L := by
  exact of_decide_eq_true (List.mem_filter.mp ((coreEdges G L).get_mem i)).2
theorem boundary_ok (i : B G L) : (G.endpoints (origB G L i)).1 ∈ L ∨ (G.endpoints (origB G L i)).2 ∈ L := by
  exact of_decide_eq_true (List.mem_filter.mp ((boundaryEdges G L).get_mem i)).2

def vidx (v : Fin G.nV) (h : v ∉ L) : V G L := idx (coreVerts G L) v (by simp [coreVerts,h])
@[simp] theorem orig_vidx (v : Fin G.nV) (h : v ∉ L) : origV G L (vidx G L v h) = v := get_idx ..

def coreGraph : Graph where
  nV := (coreVerts G L).length
  nE := (coreEdges G L).length
  endpoints i := (vidx G L _ (internal_ok G L i).1, vidx G L _ (internal_ok G L i).2)
  side v := G.side (origV G L v)
  bipartite i := by simpa using G.bipartite (origE G L i)

def Independent := ∀ e : Fin G.nE, (G.endpoints e).1 ∈ L → (G.endpoints e).2 ∉ L

theorem independent_of_spec {m k S D : ℕ} (s : LookupSeparatorSpec G m k S D) : Independent G s.lookupVerts := by
  intro e h h'; exact Finset.disjoint_left.mp s.disjoint_verts h' ((s.lookup_edges_to_subdiv e).1 h)

def host₀ (h : Independent G L) (i : B G L) : V G L :=
  let p := G.endpoints (origB G L i)
  if ha : p.1 ∈ L then vidx G L p.2 (h _ ha) else vidx G L p.1 ha

def pinEdge (h : Independent G L) (v : V G L) : Option (B G L) :=
  ((List.finRange (boundaryEdges G L).length).find? fun i => host₀ G L h i == v)

theorem port_inc (H : Graph) (u : Fin H.nV) (j : Fin (H.deg u)) :
    (H.endpoints ((H.ports u).get j)).1 = u ∨ (H.endpoints ((H.ports u).get j)).2 = u :=
  of_decide_eq_true (List.mem_filter.mp ((H.ports u).get_mem j)).2

def portIncl (v : V G L) (j : Fin ((coreGraph G L).deg v)) : Fin (G.deg (origV G L v)) :=
  let i := ((coreGraph G L).ports v).get j
  idx (G.ports (origV G L v)) (origE G L i) (by
    have hm := port_inc (coreGraph G L) v j
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange _,decide_eq_true ?_⟩
    rcases hm with h | h
    · left; simpa [coreGraph,i] using congrArg (origV G L) h
    · right; simpa [coreGraph,i] using congrArg (origV G L) h)

structure Cut (G : Graph) (L : Finset (Fin G.nV)) where
  H₀ : Graph
  boundary : List (Fin G.nE)
  host : Fin boundary.length → Fin H₀.nV
  orig : Fin H₀.nV → Fin G.nV
  incl : (v : Fin H₀.nV) → Fin (H₀.deg v) → Fin (G.deg (orig v))
  pin : Fin H₀.nV → Option (Fin boundary.length)

def cutCore (h : Independent G L) : Cut G L :=
  ⟨coreGraph G L,boundaryEdges G L,host₀ G L h,origV G L,portIncl G L,pinEdge G L h⟩

def Cut.encode (t : Cut G L) : Word := Encoding.encodeList id
  [t.H₀.encode,encodeNatListBin (List.ofFn fun i => (t.host i).val),
   encodeNatListBin (List.ofFn fun v => (t.orig v).val),encodeNatListBin (t.boundary.map Fin.val),
   encodeNatListBin (List.ofFn fun v => ((t.pin v).map (fun i => i.val + 1)).getD 0),
   Encoding.encodeList id (List.ofFn fun v => encodeNatListBin (List.ofFn fun j => (t.incl v j).val))]

theorem lookup_length : (lookupVerts G L).length = L.card := by
  have nod := (List.nodup_finRange _).filter (fun v : Fin G.nV => decide (v ∈ L))
  unfold lookupVerts
  rw [← List.toFinset_card_of_nodup nod]
  congr 1; ext; simp

def lookupIdx (i : B G L) : Fin L.card :=
  let p := G.endpoints (origB G L i)
  let v := if p.1 ∈ L then p.1 else p.2
  let hv : v ∈ L := by dsimp only [v]; split <;> grind [boundary_ok]
  (idx (lookupVerts G L) v (by simp [lookupVerts,hv])).cast (lookup_length G L)

def reattach (n : ℕ) (leaf : B G L → Fin n) : Graph where
  nV := L.card + n
  nE := (boundaryEdges G L).length
  endpoints i := ((lookupIdx G L i).castAdd n, Fin.natAdd L.card (leaf i))
  side v := decide (L.card ≤ v.val)
  bipartite i := by simp [(lookupIdx G L i).isLt]

namespace Raw
open DetDLP_W1_Queries Groundwork.PolyT
abbrev Nums := List ℕ
/-- Iterate a fixed number of fields, independent of encoded counts. -/
def field : ℕ → Word → Word
  | 0, w => first w
  | k+1, w => field k (more w)

def pack (ws : List Word) : Word := ws.flatMap (fun w => true :: frame w) ++ [false]

def graphWord (s : Word) (es : Nums) (nE : ℕ) := pack [countWord s.length,countWord nE,s,encodeNatListBin es]

/-- The edge-range fuel comes from the explicit endpoint array, never a binary header. -/
def ends (w : Word) := w5_M6Sort.decode (field 3 (field 1 w))
def sides (w : Word) := field 2 (field 1 w)
def mask (w : Word) := field 8 w
def lhs (w : Word) (e : ℕ) := (ends w).getD (2*e) 0
def rhs (w : Word) (e : ℕ) := (ends w).getD (2*e+1) 0
def vertices (w : Word) (look : Bool) := (List.range (sides w).length).filter (fun v => (mask w).getD v false == look)
def edges (w : Word) := (List.range (ends w).length).filter (fun e => decide (2*e+1 < (ends w).length))
def boundary (w : Word) (e : ℕ) := (mask w).getD (lhs w e) false || (mask w).getD (rhs w e) false
def selected (w : Word) (b : Bool) := (edges w).filter fun e => boundary w e == b
def other (w : Word) (e : ℕ) := bif (mask w).getD (lhs w e) false then rhs w e else lhs w e
def lookup (w : Word) (e : ℕ) := bif (mask w).getD (lhs w e) false then lhs w e else rhs w e
def ports (w : Word) (es : Nums) (v : ℕ) := es.filter (fun e => lhs w e == v || rhs w e == v)
def portTable (w : Word) (v : ℕ) := (ports w (selected w false) v).map fun e => (ports w (edges w) v).idxOf e

def cut (w : Word) : Word :=
  let vs := vertices w false
  let ies := selected w false
  let bs := selected w true
  let hosts := bs.map (fun e => vs.idxOf (other w e))
  let pins := (List.range vs.length).map fun v => if v ∈ hosts then hosts.idxOf v + 1 else 0
  pack [graphWord (vs.map (fun v => (sides w).getD v false))
          (ies.flatMap fun e => [vs.idxOf (lhs w e),vs.idxOf (rhs w e)]) ies.length,
        encodeNatListBin hosts, encodeNatListBin vs, encodeNatListBin bs, encodeNatListBin pins,
        pack (vs.map (fun v => encodeNatListBin (portTable w v)))]

def residual (q : Word) : Word :=
  let w := field 0 q
  let l := vertices w true
  let n := field 1 q
  let f := w5_M6Sort.decode (field 2 q)
  let bs := selected w true
  graphWord ((l.map fun _ => false) ++ (n.map fun _ => true))
    ((List.range bs.length).flatMap fun i => [l.idxOf (lookup w (bs.getD i 0)),l.length + f.getD i 0]) bs.length
end Raw

def cutCoreRaw := Raw.cut
def reattachRaw := Raw.residual
/-- The unary count allows unrestricted n, including isolated leaves. -/
def reattachInput (w : Word) (n : ℕ) (ls : List ℕ) := Encoding.encodeList id [w,List.replicate n true,encodeNatListBin ls]

end DetDLP.D4CoreCut


