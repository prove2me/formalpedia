-- Prove2me | Definitions.Def_CSL_NetworkCoding_Model_PipelineBlockCode
-- name    : CSL_NetworkCoding_Model_PipelineBlockCode
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:58:07.720434+00:00
-- url     : https://prove2.me/theorems/5dc5f1db-ff14-4eaa-b257-56ec6985e6c0
-- title:
--   Coded sorting library: NetworkCoding / Model / PipelineBlockCode
-- statement:
--   Module `CodedSorting.NetworkCoding.Model.PipelineBlockCode` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Subdivision into a genuine simple undirected graph
--
--   Each physical edge receives its own midpoint and becomes two physical edges.
--   The orientation records the coding schedule only. The underlying adjacency is
--   undirected, and the two endpoints determine a unique new physical edge, even
--   when the original network has parallel edges. Both directions share that edge.
--
--   The midpoint receives the tail's matrix label. Consequently one half has rank
--   length zero and the other has the original rank length. Local linear coding
--   is retained by forwarding the received bit at each midpoint.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.NetworkCoding.Model.PipelineBlockCode

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_NetworkCoding_Model_NetworkRates
import Mathlib.Combinatorics.SimpleGraph.Basic

section NetworkSubdivision
/-!
# Subdivision into a genuine simple undirected graph

Each physical edge receives its own midpoint and becomes two physical edges.
The orientation records the coding schedule only. The underlying adjacency is
undirected, and the two endpoints determine a unique new physical edge, even
when the original network has parallel edges. Both directions share that edge.

The midpoint receives the tail's matrix label. Consequently one half has rank
length zero and the other has the original rank length. Local linear coding
is retained by forwarding the received bit at each midpoint.
-/

set_option autoImplicit false

namespace CSL.NetworkSubdivision

open CSL.Circuit NetworkProtocol GraphRouting
open scoped BigOperators

variable {Node Edge Session I : Type*}

abbrev Vertex (Node Edge : Type*) := Node ⊕ Edge
abbrev HalfEdge (Edge : Type*) := Edge ⊕ Edge

def network (net : RankedNetwork Node Edge) :
    RankedNetwork (Vertex Node Edge) (HalfEdge Edge) where
  tail := Sum.elim (fun e => .inl (net.tail e)) Sum.inr
  head := Sum.elim Sum.inr (fun e => .inl (net.head e))
  rank := Sum.elim (fun v => 2 * net.rank v) (fun e => 2 * net.rank (net.tail e) + 1)
  forward := by
    intro e
    cases e with
    | inl e => dsimp; omega
    | inr e => dsimp; have h := net.forward e; omega

theorem tail_ne_head (net : RankedNetwork Node Edge) (e : Edge) :
    net.tail e ≠ net.head e := by
  intro h
  have hf := net.forward e
  rw [h] at hf
  omega

/-- Undirected incidence of one physical half-edge. -/
def Joins (net : RankedNetwork Node Edge) (e : HalfEdge Edge)
    (u v : Vertex Node Edge) : Prop :=
  ((network net).tail e = u ∧ (network net).head e = v) ∨
  ((network net).tail e = v ∧ (network net).head e = u)

def simpleGraph (net : RankedNetwork Node Edge) : SimpleGraph (Vertex Node Edge) where
  Adj u v := ∃ e, Joins net e u v
  symm := ⟨by
    rintro u v ⟨e, h⟩
    exact ⟨e, h.symm⟩⟩
  loopless := ⟨by
    rintro u ⟨e, h | h⟩ <;>
      exact tail_ne_head (network net) e (h.1.trans h.2.symm)⟩

/-- Subdivision removes parallel edges: an unordered endpoint pair identifies
exactly one physical half-edge. -/
theorem joins_unique (net : RankedNetwork Node Edge)
    {e f : HalfEdge Edge} {u v : Vertex Node Edge}
    (he : Joins net e u v) (hf : Joins net f u v) : e = f := by
  have h : ((network net).tail e = (network net).tail f ∧
      (network net).head e = (network net).head f) ∨
      ((network net).tail e = (network net).head f ∧
      (network net).head e = (network net).tail f) := by
    rcases he with he | he <;> rcases hf with hf | hf
    · exact Or.inl ⟨he.1.trans hf.1.symm, he.2.trans hf.2.symm⟩
    · exact Or.inr ⟨he.1.trans hf.2.symm, he.2.trans hf.1.symm⟩
    · exact Or.inr ⟨he.1.trans hf.2.symm, he.2.trans hf.1.symm⟩
    · exact Or.inl ⟨he.1.trans hf.1.symm, he.2.trans hf.2.symm⟩
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      have h' : net.tail e = net.tail f ∧ e = f := by simpa [network] using h
      exact congrArg Sum.inl h'.2
    | inr f =>
      simp only [network, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
        Sum.inr.injEq, Sum.inl_ne_inr, false_and, false_or] at h
      rcases h with ⟨h, rfl⟩
      exact False.elim (tail_ne_head net e h)
  | inr e =>
    cases f with
    | inl f =>
      simp only [network, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
        Sum.inr.injEq, Sum.inr_ne_inl, false_and, false_or] at h
      rcases h with ⟨rfl, h⟩
      exact False.elim (tail_ne_head net e h.symm)
    | inr f =>
      have h' : e = f ∧ net.head e = net.head f := by simpa [network] using h
      exact congrArg Sum.inr h'.1

theorem adjacency_iff_unique_edge (net : RankedNetwork Node Edge)
    (u v : Vertex Node Edge) :
    (simpleGraph net).Adj u v ↔ ∃! e, Joins net e u v := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, he, fun f hf => joins_unique net hf he⟩
  · rintro ⟨e, he, _⟩
    exact ⟨e, he⟩

/-- An old source leaf remains a source leaf, now incident to the first
half of its original unique edge. -/
theorem source_leaf_preserved (net : RankedNetwork Node Edge) (s : Node) (e₀ : Edge)
    (htail : net.tail e₀ = s)
    (hleaf : ∀ e, net.tail e = s ∨ net.head e = s ↔ e = e₀)
    (f : HalfEdge Edge) :
    (network net).tail f = .inl s ∨ (network net).head f = .inl s ↔
      f = .inl e₀ := by
  cases f with
  | inl e =>
    simp only [network, Sum.elim_inl, Sum.inl.injEq, Sum.inr_ne_inl, or_false]
    constructor
    · intro h
      exact (hleaf e).mp (Or.inl h)
    · rintro rfl
      exact htail
  | inr e =>
    simp only [network, Sum.elim_inr, Sum.inl.injEq, Sum.inr_ne_inl, false_or]
    constructor
    · intro h
      have he := (hleaf e).mp (Or.inr h)
      subst e
      exact tail_ne_head net e₀ (htail.trans h.symm)
    · exact False.elim

/-- Physical half-edges are in bijection with the ordinary unordered edge
set of the simple graph. Unit capacities therefore have no parallel copies. -/
def edgeToSimpleEdge (net : RankedNetwork Node Edge) (e : HalfEdge Edge) :
    (simpleGraph net).edgeSet :=
  ⟨s((network net).tail e, (network net).head e),
    ⟨e, Or.inl ⟨rfl, rfl⟩⟩⟩

theorem edgeToSimpleEdge_bijective (net : RankedNetwork Node Edge) :
    Function.Bijective (edgeToSimpleEdge net) := by
  constructor
  · intro e f h
    apply joins_unique net (u := (network net).tail f) (v := (network net).head f)
    · exact Sym2.eq_iff.mp (congrArg Subtype.val h)
    · exact Or.inl ⟨rfl, rfl⟩
  · rintro ⟨z, hz⟩
    induction z using Sym2.ind with
    | h u v =>
      rcases hz with ⟨e, he⟩
      exact ⟨e, Subtype.ext (Sym2.eq_iff.mpr he)⟩

noncomputable def physicalEdgeEquiv (net : RankedNetwork Node Edge) :
    HalfEdge Edge ≃ (simpleGraph net).edgeSet :=
  Equiv.ofBijective (edgeToSimpleEdge net) (edgeToSimpleEdge_bijective net)

def label (net : RankedNetwork Node Edge) (M : Node → Matrix I I ℚ) :
    Vertex Node Edge → Matrix I I ℚ :=
  Sum.elim M (fun e => M (net.tail e))

@[simp] theorem first_length [Fintype I] (net : RankedNetwork Node Edge)
    (M : Node → Matrix I I ℚ) (e : Edge) :
    edgeLength (network net) (label net M) (.inl e) = 0 := by
  simp [edgeLength, label, network]

@[simp] theorem second_length [Fintype I] (net : RankedNetwork Node Edge)
    (M : Node → Matrix I I ℚ) (e : Edge) :
    edgeLength (network net) (label net M) (.inr e) = edgeLength net M e := rfl

theorem total_length_preserved [Fintype I] [Fintype Edge]
    (net : RankedNetwork Node Edge) (M : Node → Matrix I I ℚ) :
    (∑ e, edgeLength (network net) (label net M) e) = ∑ e, edgeLength net M e := by
  simp [Fintype.sum_sum_type]

theorem endpoints_preserved (net : RankedNetwork Node Edge)
    (M : Node → Matrix I I ℚ) (s t : Node) :
    label net M (.inl t) - label net M (.inl s) = M t - M s := rfl

/-- An original undirected walk traverses the two halves in the appropriate
order. The half-edge identifiers do not depend on traversal direction. -/
def expandWalk (net : RankedNetwork Node Edge) {s t : Node} :
    Walk net s t → Walk (network net) (.inl s) (.inl t)
  | .nil v => Walk.nil (net := network net) (Sum.inl v)
  | .forward e rest => Walk.forward (net := network net) (Sum.inl e)
      (Walk.forward (net := network net) (Sum.inr e) (expandWalk net rest))
  | .reverse e rest => Walk.reverse (net := network net) (Sum.inr e)
      (Walk.reverse (net := network net) (Sum.inl e) (expandWalk net rest))

local instance [DecidableEq Edge] : BEq (HalfEdge Edge) :=
  ⟨fun e f => decide (e = f)⟩

local instance [DecidableEq Edge] : LawfulBEq (HalfEdge Edge) where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

theorem expandWalk_count_first [DecidableEq Edge] (net : RankedNetwork Node Edge)
    {s t : Node} (w : Walk net s t) (e : Edge) :
    (expandWalk net w).edges.count (.inl e) = w.edges.count e := by
  induction w with
  | nil v => simp [expandWalk, Walk.edges]
  | forward f rest ih =>
    simp only [expandWalk, Walk.edges, List.count_cons]
    erw [ih]
    simp [beq_iff_eq]
  | reverse f rest ih =>
    simp only [expandWalk, Walk.edges, List.count_cons]
    erw [ih]
    simp [beq_iff_eq]

theorem expandWalk_count_second [DecidableEq Edge] (net : RankedNetwork Node Edge)
    {s t : Node} (w : Walk net s t) (e : Edge) :
    (expandWalk net w).edges.count (.inr e) = w.edges.count e := by
  induction w with
  | nil v => simp [expandWalk, Walk.edges]
  | forward f rest ih =>
    simp only [expandWalk, Walk.edges, List.count_cons]
    erw [ih]
    simp [beq_iff_eq]
  | reverse f rest ih =>
    simp only [expandWalk, Walk.edges, List.count_cons]
    erw [ih]
    simp [beq_iff_eq]

/-- Any fractional routing retains its unit-capacity bounds after subdivision;
repeated traversals are counted and reverse traversals use the same half-edge. -/
theorem expanded_routing_capacity [DecidableEq Edge] {Path : Type*} [Fintype Path]
    (net : RankedNetwork Node Edge) (source sink : Path → Node)
    (walk : ∀ p, Walk net (source p) (sink p)) (flow : Path → ℝ)
    (hcapacity : ∀ e, ∑ p, flow p * (walk p).edges.count e ≤ 1) :
    ∀ e, ∑ p, flow p * (expandWalk net (walk p)).edges.count e ≤ 1 := by
  intro e
  cases e with
  | inl e => simpa only [expandWalk_count_first] using hcapacity e
  | inr e => simpa only [expandWalk_count_second] using hcapacity e

theorem depth_bound (net : RankedNetwork Node Edge) {D : ℕ}
    (hdepth : ∀ e, net.rank (net.tail e) ≤ D) :
    ∀ e, (network net).rank ((network net).tail e) ≤ 2 * D + 1 := by
  intro e
  cases e with
  | inl e => dsimp [network]; have h := hdepth e; omega
  | inr e => dsimp [network]; have h := hdepth e; omega

section LinearCode

variable (net : RankedNetwork Node Edge) (code : LinearCode net Session)

abbrev InputPort (v : Vertex Node Edge) :=
  {i : Session // Sum.inl (code.source i) = v} ⊕
    {e : HalfEdge Edge // (network net).head e = v}

abbrev OutputPort (v : Vertex Node Edge) :=
  {e : HalfEdge Edge // (network net).tail e = v}

/-- The original inputs at an old vertex are the same source bits and the
second halves of precisely its original incoming edges. -/
def inputAtOld (v : Node) :
    ({i : Session // code.source i = v} ⊕ {e : Edge // net.head e = v}) →
      InputPort net code (.inl v)
  | .inl i => .inl ⟨i.val, congrArg Sum.inl i.property⟩
  | .inr e => .inr ⟨.inr e.val, congrArg Sum.inl e.property⟩

def outputAtOld (v : Node) (e : OutputPort net (.inl v)) :
    {e : Edge // net.tail e = v} :=
  ⟨Sum.elim id id e.val, by
    rcases e with ⟨e | e, h⟩
    · exact Sum.inl.inj h
    · exact False.elim (Sum.inr_ne_inl h)⟩

def inputAtSink (i : Session) (e : {e : Edge // net.head e = code.sink i}) :
    {e : HalfEdge Edge // (network net).head e = .inl (code.sink i)} :=
  ⟨.inr e.val, congrArg Sum.inl e.property⟩

/-- The same local linear computation at old nodes; identity forwarding at
each fresh midpoint. No node is given nonlocal input bits. -/
noncomputable def codeOnSubdivision : LinearCode (network net) Session where
  source i := .inl (code.source i)
  sink i := .inl (code.sink i)
  localMap := fun v => match v with
    | .inl v =>
      (LinearMap.pi (fun e =>
        (LinearMap.proj (outputAtOld net v e)).comp (code.localMap v))).comp
          (LinearMap.pi (fun p => LinearMap.proj (inputAtOld net code v p)))
    | .inr e =>
      LinearMap.pi (fun _ =>
        LinearMap.proj (Sum.inr (⟨Sum.inl e, rfl⟩ :
          {f : HalfEdge Edge // (network net).head f = .inr e})))
  decoder i := (code.decoder i).comp
    (LinearMap.pi (fun e => LinearMap.proj (inputAtSink net code i e)))

@[simp] theorem subdivision_local_old (v : Node)
    (values : InputPort net code (.inl v) → Bit) (e : OutputPort net (.inl v)) :
    (codeOnSubdivision net code).localMap (.inl v) values e =
      code.localMap v (values ∘ inputAtOld net code v) (outputAtOld net v e) := rfl

@[simp] theorem subdivision_local_mid (e : Edge)
    (values : InputPort net code (.inr e) → Bit) (f : OutputPort net (.inr e)) :
    (codeOnSubdivision net code).localMap (.inr e) values f =
      values (.inr ⟨.inl e, rfl⟩) := rfl

/-- Both halves carry exactly the bit computed by the original local code.
This identifies recursively computed executions, not an assumed transcript. -/
theorem edgeValue_preserved (input : Session → Bit) (e : HalfEdge Edge) :
    edgeValue (network net) (codeOnSubdivision net code) input e =
      edgeValue net code input (Sum.elim id id e) := by
  apply edgeValue_unique (network net) (codeOnSubdivision net code) input
    (fun e => edgeValue net code input (Sum.elim id id e))
  intro f
  cases f with
  | inl f =>
    change edgeValue net code input f = _
    rw [edgeValue_local net code input f]
    change code.localMap (net.tail f) _ ⟨f, rfl⟩ =
      code.localMap (net.tail f) _ ⟨f, rfl⟩
    apply congrArg (fun values => code.localMap (net.tail f) values ⟨f, rfl⟩)
    funext p
    cases p <;> rfl
  | inr f => rfl

theorem correctness_preserved (hcorrect : Correct net code) :
    Correct (network net) (codeOnSubdivision net code) := by
  intro input i
  change code.decoder i (fun e =>
    edgeValue (network net) (codeOnSubdivision net code) input (.inr e.val)) = input i
  simp only [edgeValue_preserved, Sum.elim_inr, id_eq]
  exact hcorrect input i

/-- The subdivided simple graph supports the same independent messages.
Its finite pipeline has unit edge capacity, causal local computations,
and horizon `k + (2*D+1)`. -/
theorem finite_simple_pipeline {k D : ℕ} (hcorrect : Correct net code)
    (hdepth : ∀ e, net.rank (net.tail e) ≤ D)
    (inputs : Fin k → Session → Bit) :
    (∀ e time,
      (Finset.univ.filter (fun batch : Fin k =>
        sendTime (network net) batch e = time)).card ≤ 1) ∧
    (∀ (batch : Fin k) e incoming,
      (network net).head incoming = (network net).tail e →
      sendTime (network net) batch incoming < sendTime (network net) batch e) ∧
    (∀ (batch : Fin k) e, sendTime (network net) batch e < k + (2 * D + 1)) ∧
    (∀ (batch : Fin k) i, (codeOnSubdivision net code).decoder i (fun incoming =>
      (packet (network net) (codeOnSubdivision net code) inputs incoming.val
        (sendTime (network net) batch incoming.val)).getD 0) = inputs batch i) :=
  finite_pipeline (network net) (codeOnSubdivision net code)
    (correctness_preserved net code hcorrect) (depth_bound net hdepth) inputs

end LinearCode

end CSL.NetworkSubdivision
end NetworkSubdivision

section PipelineBlockCode
/-!
# Actual packet pipelining as a stateful causal network protocol

Each node stores only its own source messages and bits received on incident
edges. A fixed clock assigns batch `b` on edge `e` to time `b + rank(tail e)`.
This implements the previously verified linear code in `NetworkCut.Protocol`,
the same model used for arbitrary nonlinear coding upper bounds.
-/

set_option autoImplicit false

namespace CSL.PipelineBlockCode

open CSL.Circuit CSL.NetworkProtocol

private def bitOfBool : Bool → Bit | false => 0 | true => 1
private def boolOfBit (x : Bit) : Bool := decide (x ≠ 0)

@[simp] private theorem bitOfBool_boolOfBit : ∀ x : Bit, bitOfBool (boolOfBit x) = x := by decide
@[simp] private theorem boolOfBit_bitOfBool : ∀ b : Bool, boolOfBit (bitOfBool b) = b := by decide

variable {Node Edge Session : Type}
variable (net : RankedNetwork Node Edge) (code : LinearCode net Session) (k : ℕ)

abbrev LocalState := (Session → Fin k → Bit) × (Edge → Fin k → Bit)

noncomputable section

def protocol : NetworkCut.Protocol net (LocalState (Edge := Edge) (Session := Session) k) := by
  classical
  exact {
    forward := fun _ _ => true
    emit := fun t v state e =>
      if he : net.tail e = v then
        if hb : net.rank v ≤ t ∧ t - net.rank v < k then
          boolOfBit (code.localMap v (fun port => match port with
            | .inl i => state.1 i.val ⟨t - net.rank v, hb.2⟩
            | .inr incoming => state.2 incoming.val ⟨t - net.rank v, hb.2⟩) ⟨e,he⟩)
        else false
      else false
    update := fun t v state received =>
      (state.1, fun e b =>
        if net.head e = v ∧ t = sendTime net b e then bitOfBool (received e)
        else state.2 e b)
  }

def localInitial (v : Node)
    (inputs : {i : Session // code.source i = v} → Fin k → Bool) :
    LocalState (Edge := Edge) (Session := Session) k := by
  classical
  exact (fun i b => if h : code.source i = v then bitOfBool (inputs ⟨i,h⟩ b) else 0,
    fun _ _ => 0)

def initial (inputs : Session → Fin k → Bool) (v : Node) :
    LocalState (Edge := Edge) (Session := Session) k :=
  localInitial net code k v (fun i => inputs i.val)

def statesAt (inputs : Session → Fin k → Bool) (n : ℕ) :=
  NetworkCut.run net (protocol net code k) n 0 (initial net code k inputs)

/-- One extra round updates the state reached after all preceding rounds. -/
theorem run_succ {S : Type*} (p : NetworkCut.Protocol net S)
    (n t : ℕ) (states : Node → S) :
    NetworkCut.run net p (n+1) t states =
      NetworkCut.step net p (t+n) (NetworkCut.run net p n t states) := by
  induction n generalizing t states with
  | zero => simp only [NetworkCut.run, Nat.add_zero]
  | succ n ih =>
    change NetworkCut.run net p (n+1) (t+1) (NetworkCut.step net p t states) =
      NetworkCut.step net p (t+(n+1))
        (NetworkCut.run net p n (t+1) (NetworkCut.step net p t states))
    rw [ih]
    simp only [Nat.add_right_comm, Nat.add_assoc]

theorem statesAt_succ (inputs : Session → Fin k → Bool) (n : ℕ) :
    statesAt net code k inputs (n+1) =
      NetworkCut.step net (protocol net code k) n (statesAt net code k inputs n) := by
  simpa only [statesAt, Nat.zero_add] using
    run_succ net (protocol net code k) n 0 (initial net code k inputs)

theorem message_at_sendTime (states : Node → LocalState (Edge := Edge) (Session := Session) k)
    (input : Session → Bit) (b : Fin k) (e : Edge)
    (hs : ∀ i, code.source i = net.tail e → (states (net.tail e)).1 i b = input i)
    (hi : ∀ incoming, net.head incoming = net.tail e →
      (states (net.tail e)).2 incoming b = edgeValue net code input incoming) :
    NetworkCut.message net (protocol net code k) (sendTime net b e) states e =
      boolOfBit (edgeValue net code input e) := by
  classical
  have ht : net.rank (net.tail e) ≤ sendTime net b e ∧
      sendTime net b e - net.rank (net.tail e) < k := by
    simp [sendTime, b.isLt]
  try dsimp only [NetworkCut.message, protocol]
  simp only [Bool.true_eq, ite_true, dif_pos rfl, dif_pos ht]
  simp only [sendTime, Nat.add_sub_cancel_right]
  rw [edgeValue_local]
  apply congrArg boolOfBit
  apply congrArg (fun values => code.localMap (net.tail e) values ⟨e,rfl⟩)
  funext port
  cases port with
  | inl i => exact hs i.val i.property
  | inr incoming => exact hi incoming.val incoming.property

/-- The first component remains local source data. The second contains the
correct value for every packet that has already arrived at this node. -/
theorem executionInvariant (inputs : Session → Fin k → Bool) (n : ℕ) :
    (∀ v i, code.source i = v → ∀ b,
      (statesAt net code k inputs n v).1 i b = bitOfBool (inputs i b)) ∧
    (∀ v e, net.head e = v → ∀ b,
      sendTime net b e < n →
      (statesAt net code k inputs n v).2 e b =
        edgeValue net code (fun i => bitOfBool (inputs i b)) e) := by
  classical
  induction n with
  | zero =>
    constructor
    · intro v i hi b
      simp only [statesAt, NetworkCut.run, initial, localInitial, dif_pos hi]
    · intro v e he b ht
      exact False.elim (Nat.not_lt_zero _ ht)
  | succ n ih =>
    rw [statesAt_succ]
    constructor
    · intro v i hi b
      change (statesAt net code k inputs n v).1 i b = _
      exact ih.1 v i hi b
    · intro v e he b ht
      change (if net.head e = v ∧ n = sendTime net b e then
        bitOfBool (if NetworkCut.Incident net e v then
          NetworkCut.message net (protocol net code k) n (statesAt net code k inputs n) e
          else false)
        else (statesAt net code k inputs n v).2 e b) = _
      by_cases hn : n = sendTime net b e
      · have hinc : NetworkCut.Incident net e v := Or.inr he
        simp only [he, hn, and_self, ↓reduceIte, hinc]
        rw [message_at_sendTime net code k _ _ b e]
        · exact bitOfBool_boolOfBit _
        · intro i hsource
          simpa only [hn] using ih.1 _ i hsource b
        · intro incoming hconnect
          have htime : sendTime net b incoming < n := by
            rw [hn]
            exact incoming_before_outgoing net b e incoming hconnect
          simpa only [hn] using ih.2 _ incoming hconnect b htime
      · simp only [show ¬ (net.head e = v ∧ n = sendTime net b e) from fun h => hn h.2,
          ↓reduceIte]
        apply ih.2 v e he b
        omega

/-- Decode every batch using only the final local mailbox at its own sink. -/
def localDecode (i : Session) (state : LocalState (Edge := Edge) (Session := Session) k)
    (b : Fin k) : Bool :=
  boolOfBit (code.decoder i (fun incoming => state.2 incoming.val b))

theorem pipeline_correct {D : ℕ} (hcorrect : Correct net code)
    (hdepth : ∀ e, net.rank (net.tail e) ≤ D)
    (inputs : Session → Fin k → Bool) (i : Session) :
    localDecode net code k i (statesAt net code k inputs (k+D) (code.sink i)) = inputs i := by
  funext b
  unfold localDecode
  have hmail : (fun incoming : {e : Edge // net.head e = code.sink i} =>
      (statesAt net code k inputs (k+D) (code.sink i)).2 incoming.val b) =
      (fun incoming => edgeValue net code (fun j => bitOfBool (inputs j b)) incoming.val) := by
    funext incoming
    exact (executionInvariant net code k inputs (k+D)).2
      _ incoming.val incoming.property b (every_packet_before_horizon net hdepth b incoming.val)
  rw [hmail, hcorrect]
  exact boolOfBit_bitOfBool _

/-- A block code in exactly the operational class used for capacity upper
bounds, with arbitrary independent k-bit inputs and duration k+D. -/
def blockCode {D : ℕ} (hcorrect : Correct net code)
    (hdepth : ∀ e, net.rank (net.tail e) ≤ D) :
    NetworkRates.BlockCode net code.source code.sink k (k+D) where
  State := LocalState (Edge := Edge) (Session := Session) k
  protocol := protocol net code k
  initial := localInitial net code k
  decode := localDecode net code k
  correct := pipeline_correct net code k hcorrect hdepth

open CSL.CircuitProgram CSL.ProgramNetwork

/-- The literal three-round XOR construction as a genuine finite BlockCode. -/
def actualBlockCode (d k : ℕ) :
    NetworkRates.BlockCode (actualNetwork d) (actualCode d).source (actualCode d).sink
      k (k + (globalProgram d).length) :=
  blockCode (actualNetwork d) (actualCode d) k (actualCode_correct d)
    (depth_bound (globalProgram d))

/-- Actual finite, simultaneously achievable rates on the manuscript's graph. -/
theorem actual_rate_achievable (d k : ℕ) (hk : 0 < k) :
    NetworkRates.Achievable (actualNetwork d) (actualCode d).source (actualCode d).sink
      ((k : ℝ) / (k + (globalProgram d).length)) := by
  refine ⟨k, k + (globalProgram d).length, by omega, ⟨actualBlockCode d k⟩, ?_⟩
  simp only [Nat.cast_add]

/-- Eliminating parallel edges preserves the same operational block-code
model, with only the fixed pipeline latency increased. -/
def subdivisionBlockCode {D : ℕ} (hcorrect : Correct net code)
    (hdepth : ∀ e, net.rank (net.tail e) ≤ D) :
    NetworkRates.BlockCode (NetworkSubdivision.network net)
      (fun i => Sum.inl (code.source i)) (fun i => Sum.inl (code.sink i))
      k (k + (2*D+1)) :=
  blockCode (NetworkSubdivision.network net)
    (NetworkSubdivision.codeOnSubdivision net code) k
    (NetworkSubdivision.correctness_preserved net code hcorrect)
    (NetworkSubdivision.depth_bound net hdepth)

/-- A real block code on the simple undirected subdivision of the manuscript
network, simultaneously carrying every independent auxiliary/data message. -/
def actualSimpleBlockCode (d k : ℕ) :
    NetworkRates.BlockCode (NetworkSubdivision.network (actualNetwork d))
      (fun i => Sum.inl ((actualCode d).source i))
      (fun i => Sum.inl ((actualCode d).sink i))
      k (k + (2 * (globalProgram d).length + 1)) :=
  subdivisionBlockCode (actualNetwork d) (actualCode d) k
    (actualCode_correct d) (ProgramNetwork.depth_bound (globalProgram d))

theorem actual_simple_rate_achievable (d k : ℕ) (hk : 0 < k) :
    NetworkRates.Achievable (NetworkSubdivision.network (actualNetwork d))
      (fun i => Sum.inl ((actualCode d).source i))
      (fun i => Sum.inl ((actualCode d).sink i))
      ((k : ℝ) / (k + (2 * (globalProgram d).length + 1))) := by
  refine ⟨k, k + (2 * (globalProgram d).length + 1), by omega,
    ⟨actualSimpleBlockCode d k⟩, ?_⟩
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

end
end CSL.PipelineBlockCode
end PipelineBlockCode


