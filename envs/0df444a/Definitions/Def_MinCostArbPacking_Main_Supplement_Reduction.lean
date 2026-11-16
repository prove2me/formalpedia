-- Prove2me | Definitions.Def_MinCostArbPacking_Main_Supplement_Reduction
-- name    : MinCostArbPacking_Main_Supplement_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:47:00.040759+00:00
-- url     : https://prove2.me/theorems/fbd0b60d-8307-4942-8182-5735010273d9
-- title:
--   Algorithm 4 flow network and inherited-edge contraction data
-- statement:
--   For each current edge e with endpoints u,v, the flow network has source s, edge node x_e, vertex nodes and sink t. The arcs s→x_e have capacity one and cost pos(e); x_e→u and x_e→v have capacity one and cost zero; v→t has cost zero and capacity
--
--   $$\min\{k,\deg(v)\}.$$
--
--   Positions start at one in the common edge order. Node and arc identities are explicit finite sums, relabelled into the general integral-network type. This defines network data; forming and encoding it within a program requires interpreter instructions. Isolated vertices may be removed before encoding an actual flow call. The inherited order moves R to the front while preserving the order within R and its complement. A contraction record stores the current selected set and forests; its internal restrictions are saved, and its crossing edges are inherited. No optimality, decomposition validity or progress is assumed by this data type.
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), Algorithm 4, §6.2.2, p. 30–32

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Supplement_Weighted
import Definitions.Def_MinCostArbPacking_Main_Supplement_IntegralFlow
set_option autoImplicit false
noncomputable section
open Classical

namespace MinCostArbPacking.Main.Supplement

/-! Supporting data of Algorithm 4, pp.30–32, not an assumed-correct reduction or oracle.
The flow graph below retains every endpoint; a program may remove isolated vertices before
encoding it, as required for the O(m) network dimensions in (1.2). -/

/-- Source, one node per edge, one per vertex, and sink. -/
abbrev FlowNode (X : DigraphInput) := Unit ⊕ (Fin X.m ⊕ (Fin X.n ⊕ Unit))

/-- Source-edge arcs, the two endpoint arcs, and vertex-sink arcs (all have distinct identities). -/
abbrev FlowArc (X : DigraphInput) := Fin X.m ⊕ ((Fin X.m × Bool) ⊕ Fin X.n)

def flowSrc (X : DigraphInput) : FlowNode X := .inl ()
def flowSnk (X : DigraphInput) : FlowNode X := .inr (.inr (.inr ()))
def flowEdge {X : DigraphInput} (e : Fin X.m) : FlowNode X := .inr (.inl e)
def flowVertex {X : DigraphInput} (v : Fin X.n) : FlowNode X := .inr (.inr (.inl v))

/-- The paper's source→x_e→endpoint→sink network. -/
def flowGraph (X : DigraphInput) : Digraph (FlowNode X) (FlowArc X) where
  tail a := match a with
    | .inl _ => flowSrc X
    | .inr (.inl (e, _)) => flowEdge e
    | .inr (.inr v) => flowVertex v
  head a := match a with
    | .inl e => flowEdge e
    | .inr (.inl (e, b)) => flowVertex (if b then X.head e else X.tail e)
    | .inr (.inr _) => flowSnk X

/-- The usual undirected degree (a loop contributes twice). -/
def degree (X : DigraphInput) (v : Fin X.n) : ℕ :=
  (Finset.univ.filter (fun e => X.tail e = v)).card +
    (Finset.univ.filter (fun e => X.head e = v)).card

def flowCapacity (X : DigraphInput) : FlowArc X → ℕ
  | .inr (.inr v) => min X.k (degree X v)
  | _ => 1

/-- The position of e in the current order, starting at one. -/
def position {m : ℕ} (ord : Equiv.Perm (Fin m)) (e : Fin m) : ℕ := (ord.symm e).val + 1

/-- Integer flow costs: pos(e) only on source arcs, zero elsewhere. -/
def flowCost (X : DigraphInput) (ord : Equiv.Perm (Fin X.m)) : FlowArc X → ℤ
  | .inl e => position ord e
  | _ => 0

/-- Finite relabelling into the general integral network type. This is data, not a machine step. -/
def flowNetwork (X : DigraphInput) (ord : Equiv.Perm (Fin X.m)) : IntegralNetwork where
  n := Fintype.card (FlowNode X)
  m := Fintype.card (FlowArc X)
  G := ⟨fun e => Fintype.equivFin _ ((flowGraph X).tail ((Fintype.equivFin _).symm e)),
    fun e => Fintype.equivFin _ ((flowGraph X).head ((Fintype.equivFin _).symm e))⟩
  src := Fintype.equivFin _ (flowSrc X)
  snk := Fintype.equivFin _ (flowSnk X)
  cap e := flowCapacity X ((Fintype.equivFin _).symm e)
  c e := flowCost X ord ((Fintype.equivFin _).symm e)

/-- Move inherited R to the front, preserving the relative order within both parts. -/
def inheritedOrder {m : ℕ} (ord : Equiv.Perm (Fin m)) (R : Finset (Fin m)) : List (Fin m) :=
  let es := (List.finRange m).map ord
  es.filter (fun e => e ∈ R) ++ es.filter (fun e => e ∉ R)

/-- Saved internal trees of one contraction stage. No correctness or progress is built in. -/
structure ContractionData (X : DigraphInput) where
  phi : Finset (Fin X.m)
  forests : Fin X.k → Finset (Fin X.m)

/-- Trees to save inside a given block. -/
def ContractionData.saved {X : DigraphInput} (D : ContractionData X) (T : Finset (Fin X.n))
    (i : Fin X.k) : Finset (Fin X.m) := X.G.induced (D.forests i) T

/-- Edges inherited after contracting the phi-tight blocks. -/
def ContractionData.inherited {X : DigraphInput} (D : ContractionData X) : Finset (Fin X.m) :=
  X.G.crossingPart X.k D.phi

end MinCostArbPacking.Main.Supplement


