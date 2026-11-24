-- Prove2me | Definitions.Def_CSL_NetworkCoding_Model_NetworkRates
-- name    : CSL_NetworkCoding_Model_NetworkRates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:46:26.290636+00:00
-- url     : https://prove2.me/theorems/62dce6c7-0335-493f-97de-0e2191efb44e
-- title:
--   Coded sorting library: NetworkCoding / Model / NetworkRates
-- statement:
--   Module `CodedSorting.NetworkCoding.Model.NetworkRates` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # A deterministic one-bit cut, including interaction
--
--   The two sides may have arbitrary states and perform arbitrary computation.
--   Only the sender schedule is fixed publicly; at every time one bit crosses the
--   cut, in either direction. The actual execution is defined recursively.
--   Correct recovery of k independent bits on the other side forces k ≤ T.
--
--   This proves the cut channel's information bound. Applying it to an entire
--   network requires identifying its source-leaf execution with this interface;
--   the existence of such a correspondence is not postulated here.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.NetworkCoding.Model.NetworkRates

import Definitions.Def_CSL_Compat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_CSL_Circuit_Labels_Framework_RankMetric
import Mathlib.Data.List.Count
import Definitions.Def_CSL_Circuit_NetworkModel_Framework_ProgramNetwork
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

section CutCapacity
/-!
# A deterministic one-bit cut, including interaction

The two sides may have arbitrary states and perform arbitrary computation.
Only the sender schedule is fixed publicly; at every time one bit crosses the
cut, in either direction. The actual execution is defined recursively.
Correct recovery of k independent bits on the other side forces k ≤ T.

This proves the cut channel's information bound. Applying it to an entire
network requires identifying its source-leaf execution with this interface;
the existence of such a correspondence is not postulated here.
-/

namespace CSL.CutCapacity

variable {Left Right : Type*}

structure Protocol (Left Right : Type*) where
  sendLeft : ℕ → Bool
  leftBit : ℕ → Left → Bool
  rightBit : ℕ → Right → Bool
  updateLeft : ℕ → Left → Bool → Left
  updateRight : ℕ → Right → Bool → Right

def emitted (p : Protocol Left Right) (time : ℕ) (l : Left) (r : Right) : Bool :=
  if p.sendLeft time then p.leftBit time l else p.rightBit time r

/-- The trace contains exactly one bit per time step. The public direction is
not an additional data-carrying channel. -/
def run (p : Protocol Left Right) : (n : ℕ) → ℕ → Left → Right →
    (Fin n → Bool) × Left × Right
  | 0, _, l, r => (Fin.elim0, l, r)
  | n+1, t, l, r =>
      let b := emitted p t l r
      let out := run p n (t+1) (p.updateLeft t l b) (p.updateRight t r b)
      (Fin.cons b out.1, out.2)

/-- The right side can replay its state using only its initial state and the
actual cut transcript, independently of the left initial state. -/
def replayRight (p : Protocol Left Right) : (n : ℕ) → ℕ → Right →
    (Fin n → Bool) → Right
  | 0, _, r, _ => r
  | n+1, t, r, bits =>
      replayRight p n (t+1) (p.updateRight t r (bits 0)) (Fin.tail bits)

theorem right_eq_replay (p : Protocol Left Right) (n t : ℕ) (l : Left) (r : Right) :
    (run p n t l r).2.2 = replayRight p n t r (run p n t l r).1 := by
  induction n generalizing t l r with
  | zero => rfl
  | succ n ih =>
    simp only [run, replayRight, Fin.cons_zero, Fin.tail_cons]
    exact ih _ _ _

theorem equal_trace_equal_right (p : Protocol Left Right) (n t : ℕ)
    (l l' : Left) (r : Right) (he : (run p n t l r).1 = (run p n t l' r).1) :
    (run p n t l r).2.2 = (run p n t l' r).2.2 := by
  rw [right_eq_replay, right_eq_replay, he]

theorem recoverable_messages_bound {Message : Type*} [Fintype Message]
    (p : Protocol Left Right) (n : ℕ) (initialLeft : Message → Left)
    (initialRight : Right) (decode : Right → Message)
    (correct : ∀ x, decode (run p n 0 (initialLeft x) initialRight).2.2 = x) :
    Fintype.card Message ≤ 2^n := by
  have hinj : Function.Injective
      (fun x => (run p n 0 (initialLeft x) initialRight).1) := by
    intro x y h
    have he := equal_trace_equal_right p n 0 (initialLeft x) (initialLeft y) initialRight h
    have hd := congrArg decode he
    simpa only [correct] using hd
  have hc := Fintype.card_le_of_injective _ hinj
  simpa using hc

theorem recovered_bits_le_steps (p : Protocol Left Right) (k n : ℕ)
    (initialLeft : (Fin k → Bool) → Left) (initialRight : Right)
    (decode : Right → Fin k → Bool)
    (correct : ∀ x, decode (run p n 0 (initialLeft x) initialRight).2.2 = x) :
    k ≤ n := by
  have hc := recoverable_messages_bound p n initialLeft initialRight decode correct
  have hp : 2^k ≤ 2^n := by simpa using hc
  by_contra hn
  have hkn : n < k := by omega
  have hlt : 2^n < 2^k := Nat.pow_lt_pow_right (by decide) hkn
  omega

end CSL.CutCapacity
end CutCapacity

section GraphRouting
/-!
# Undirected walks and matrix-label routing bounds

`RankedNetwork` orients physical edges only for executing the code. Routing
below may traverse each edge in either direction. Both directions use the
SAME edge identifier and share its capacity. Arbitrary repeated edges are
counted with multiplicity; no simple-path assumption is used.
-/

namespace CSL.GraphRouting

open NetworkProtocol
open scoped BigOperators Matrix

universe u v
variable {Node : Type u} {Edge : Type v} {I Session Path : Type*}

inductive Walk (net : RankedNetwork Node Edge) : Node → Node → Type (max u v)
  | nil (v : Node) : Walk net v v
  | forward (e : Edge) {t : Node} (rest : Walk net (net.head e) t) :
      Walk net (net.tail e) t
  | reverse (e : Edge) {t : Node} (rest : Walk net (net.tail e) t) :
      Walk net (net.head e) t

def Walk.edges {net : RankedNetwork Node Edge} {s t : Node} :
    Walk net s t → List Edge
  | .nil _ => []
  | .forward e rest => e :: rest.edges
  | .reverse e rest => e :: rest.edges

variable (net : RankedNetwork Node Edge) [Fintype I]
variable (label : Node → Matrix I I ℚ)

noncomputable def edgeLength (e : Edge) : ℕ :=
  (label (net.head e) - label (net.tail e)).rank

theorem walk_rank_bound {s t : Node} (w : Walk net s t) :
    (label t - label s).rank ≤ (w.edges.map (edgeLength net label)).sum := by
  induction w with
  | nil v => simp [Walk.edges]
  | @forward e t w ih =>
    have he : label t - label (net.tail e) =
        (label t - label (net.head e)) + (label (net.head e) - label (net.tail e)) := by abel
    have hb := RankMetric.matrix_rank_add_le
      (label t - label (net.head e)) (label (net.head e) - label (net.tail e))
    rw [he]
    simp only [Walk.edges, List.map_cons, List.sum_cons, edgeLength]
    omega
  | @reverse e t w ih =>
    have he : label t - label (net.head e) =
        (label t - label (net.tail e)) + (label (net.tail e) - label (net.head e)) := by abel
    have hb := RankMetric.matrix_rank_add_le
      (label t - label (net.tail e)) (label (net.tail e) - label (net.head e))
    rw [RankMetric.matrix_rank_sub_symm (label (net.tail e)) (label (net.head e))] at hb
    rw [he]
    simp only [Walk.edges, List.map_cons, List.sum_cons, edgeLength]
    omega

theorem list_weight_eq_count_sum [Fintype Edge] [DecidableEq Edge]
    (weight : Edge → ℕ) (es : List Edge) :
    (es.map weight).sum = ∑ e, weight e * es.count e := by
  induction es with
  | nil => simp
  | cons a es ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.count_cons]
    simp only [Nat.mul_add, Finset.sum_add_distrib]
    simp [Nat.add_comm]

theorem walk_length_bound [Fintype Edge] [DecidableEq Edge] [DecidableEq I]
    {s t : Node} (w : Walk net s t) (he : label t - label s = 1) :
    Fintype.card I ≤ ∑ e, edgeLength net label e * w.edges.count e := by
  have hb := walk_rank_bound net label w
  rw [he, Matrix.rank_one, list_weight_eq_count_sum] at hb
  exact hb

/-- The common routing bound now follows from genuine graph walks and their
capacity constraints. Endpoint distance is derived, not assumed per path. -/
theorem common_routing_bound [Fintype Edge] [DecidableEq Edge] [DecidableEq I]
    [Fintype Session] [DecidableEq Session] [Fintype Path]
    (source sink : Session → Node)
    (endpoints : ∀ i, label (sink i) - label (source i) = 1)
    (owner : Path → Session)
    (walk : ∀ p, Walk net (source (owner p)) (sink (owner p)))
    (flow : Path → ℝ) (rate : ℝ)
    (hI : 0 < Fintype.card I) (hS : 0 < Fintype.card Session)
    (hflow : ∀ p, 0 ≤ flow p)
    (capacity : ∀ e, ∑ p, flow p * ((walk p).edges.count e : ℝ) ≤ 1)
    (sessions : ∀ i, rate ≤ ∑ p, if owner p = i then flow p else 0) :
    rate ≤ (∑ e, (edgeLength net label e : ℝ)) /
      ((Fintype.card Session : ℝ) * (Fintype.card I : ℝ)) := by
  have paths (p : Path) : (Fintype.card I : ℝ) ≤
      ∑ e, (edgeLength net label e : ℝ) * ((walk p).edges.count e : ℝ) := by
    exact_mod_cast walk_length_bound net label (walk p) (endpoints (owner p))
  have ht := RankMetric.session_total_flow owner flow rate sessions
  have hi : (0 : ℝ) < Fintype.card I := by exact_mod_cast hI
  have hs : (0 : ℝ) < Fintype.card Session := by exact_mod_cast hS
  have hb := RankMetric.common_rate_bound flow (fun e => (edgeLength net label e : ℝ))
    (fun _ => 1) (fun p e => (walk p).edges.count e)
    (Fintype.card I : ℝ) (Fintype.card Session : ℝ) rate hi hs hflow
    (fun e => Nat.cast_nonneg _) paths capacity ht
  simpa only [mul_one] using hb

end CSL.GraphRouting
end GraphRouting

section NetworkCut
/-!
# The source-leaf cut for arbitrary causal binary network protocols

Local state and computation are unrestricted and need not be linear. Each
physical undirected edge carries one bit per synchronous step, with a public
choice of direction. A node's update sees only its own state and incident
edge bits. We project this actual execution to the two-party cut channel;
we do not assume a transcript/information inequality for the network.
-/

set_option autoImplicit false

namespace CSL.NetworkCut

open CSL.NetworkProtocol

variable {Node Edge State : Type*}

structure Protocol (net : RankedNetwork Node Edge) (State : Type*) where
  forward : ℕ → Edge → Bool
  emit : ℕ → Node → State → Edge → Bool
  update : ℕ → Node → State → (Edge → Bool) → State

variable (net : RankedNetwork Node Edge)

 def Incident (e : Edge) (v : Node) : Prop := net.tail e = v ∨ net.head e = v

noncomputable section

variable (p : Protocol net State)

def message (time : ℕ) (states : Node → State) (e : Edge) : Bool :=
  if p.forward time e then p.emit time (net.tail e) (states (net.tail e)) e
  else p.emit time (net.head e) (states (net.head e)) e

def step (time : ℕ) (states : Node → State) (v : Node) : State := by
  classical
  exact p.update time v (states v)
    (fun e => if Incident net e v then message net p time states e else false)

def run : ℕ → ℕ → (Node → State) → (Node → State)
  | 0, _, states => states
  | n+1, t, states => run n (t+1) (step net p t states)

variable (source : Node)

abbrev Away := {v : Node // v ≠ source}

def glue (left : State) (right : Away source → State) (v : Node) : State := by
  classical
  exact if h : v = source then left else right ⟨v, h⟩

@[simp] theorem glue_at_source (left : State) (right : Away source → State) :
    glue source left right source = left := by simp [glue]

@[simp] theorem glue_away (left : State) (right : Away source → State)
    (v : Away source) : glue source left right v.val = right v := by
  simp [glue, v.property]

variable (cutEdge : Edge) (htail : net.tail cutEdge = source)
variable (hhead : net.head cutEdge ≠ source)
variable (hleaf : ∀ e, Incident net e source ↔ e = cutEdge)

def remoteMessage (time : ℕ) (right : Away source → State) (e : Edge) : Bool := by
  classical
  exact if p.forward time e then
    if h : net.tail e = source then false else
      p.emit time (net.tail e) (right ⟨net.tail e, h⟩) e
  else if h : net.head e = source then false else
      p.emit time (net.head e) (right ⟨net.head e, h⟩) e

def asCut : CutCapacity.Protocol State (Away source → State) := by
  classical
  exact {
    sendLeft := fun t => p.forward t cutEdge
    leftBit := fun t l => p.emit t source l cutEdge
    rightBit := fun t r => p.emit t (net.head cutEdge) (r ⟨net.head cutEdge, hhead⟩) cutEdge
    updateLeft := fun t l b => p.update t source l
      (fun e => if e = cutEdge then b else false)
    updateRight := fun t r b v => p.update t v.val (r v)
      (fun e => if Incident net e v.val then
        if e = cutEdge then b else remoteMessage net p source t r e
        else false)
  }

include htail in
theorem message_cut (time : ℕ) (left : State) (right : Away source → State) :
    message net p time (glue source left right) cutEdge =
      CutCapacity.emitted (asCut net p source cutEdge hhead) time left right := by
  classical
  simp only [message, asCut, CutCapacity.emitted, htail, glue_at_source]
  split <;> simp_all [glue]

include hleaf in
theorem message_off_cut (time : ℕ) (left : State) (right : Away source → State)
    (e : Edge) (he : e ≠ cutEdge) :
    message net p time (glue source left right) e =
      remoteMessage net p source time right e := by
  have ht : net.tail e ≠ source := fun h => he ((hleaf e).mp (Or.inl h))
  have hh : net.head e ≠ source := fun h => he ((hleaf e).mp (Or.inr h))
  simp [message, remoteMessage, glue, ht, hh]

include htail hleaf in
theorem step_source (time : ℕ) (left : State) (right : Away source → State) :
    step net p time (glue source left right) source =
      (asCut net p source cutEdge hhead).updateLeft time left
        (CutCapacity.emitted (asCut net p source cutEdge hhead) time left right) := by
  classical
  simp only [step, glue_at_source, asCut]
  apply congrArg (p.update time source left)
  funext e
  by_cases he : e = cutEdge
  · subst e
    simp only [(hleaf cutEdge).mpr rfl, ↓reduceIte]
    exact message_cut net p source cutEdge htail hhead time left right
  · simp only [he, ↓reduceIte, show ¬ Incident net e source from fun h => he ((hleaf e).mp h)]

include htail hleaf in
theorem step_away (time : ℕ) (left : State) (right : Away source → State)
    (v : Away source) :
    step net p time (glue source left right) v.val =
      (asCut net p source cutEdge hhead).updateRight time right
        (CutCapacity.emitted (asCut net p source cutEdge hhead) time left right) v := by
  classical
  simp only [step, glue_away, asCut]
  apply congrArg (p.update time v.val (right v))
  funext e
  by_cases hi : Incident net e v.val
  · simp only [hi, ↓reduceIte]
    by_cases he : e = cutEdge
    · subst e
      simp only [↓reduceIte]
      exact message_cut net p source cutEdge htail hhead time left right
    · simp only [he, ↓reduceIte]
      exact message_off_cut net p source cutEdge hleaf time left right e he
  · simp only [hi, ↓reduceIte]

include htail hleaf in
theorem step_glue (time : ℕ) (left : State) (right : Away source → State) :
    step net p time (glue source left right) =
      let b := CutCapacity.emitted (asCut net p source cutEdge hhead) time left right
      glue source ((asCut net p source cutEdge hhead).updateLeft time left b)
        ((asCut net p source cutEdge hhead).updateRight time right b) := by
  classical
  funext v
  by_cases hv : v = source
  · subst v
    rw [glue_at_source]
    exact step_source net p source cutEdge htail hhead hleaf time left right
  · change step net p time (glue source left right) v = _
    rw [show glue source
      ((asCut net p source cutEdge hhead).updateLeft time left
        (CutCapacity.emitted (asCut net p source cutEdge hhead) time left right))
      ((asCut net p source cutEdge hhead).updateRight time right
        (CutCapacity.emitted (asCut net p source cutEdge hhead) time left right)) v =
      (asCut net p source cutEdge hhead).updateRight time right
        (CutCapacity.emitted (asCut net p source cutEdge hhead) time left right) ⟨v,hv⟩
      from glue_away source _ _ ⟨v,hv⟩]
    exact step_away net p source cutEdge htail hhead hleaf time left right ⟨v,hv⟩

include htail hleaf in
/-- Actual network execution equals the two-party execution after merging
all non-source vertices into its right state. This also permits feedback. -/
theorem run_glue (n time : ℕ) (left : State) (right : Away source → State) :
    run net p n time (glue source left right) =
      glue source
        (CutCapacity.run (asCut net p source cutEdge hhead) n time left right).2.1
        (CutCapacity.run (asCut net p source cutEdge hhead) n time left right).2.2 := by
  induction n generalizing time left right with
  | zero => rfl
  | succ n ih =>
    simp only [run, CutCapacity.run]
    rw [step_glue net p source cutEdge htail hhead hleaf]
    exact ih _ _ _

include htail hhead hleaf in
/-- The network bound follows from its concrete cut execution. Neither the
local maps nor the decoder are assumed to be linear. -/
theorem recovered_bits_le_steps (k n : ℕ)
    (initialLeft : (Fin k → Bool) → State) (initialRight : Away source → State)
    (sink : Away source) (decode : State → Fin k → Bool)
    (correct : ∀ x,
      decode (run net p n 0 (glue source (initialLeft x) initialRight) sink.val) = x) :
    k ≤ n := by
  apply CutCapacity.recovered_bits_le_steps
    (asCut net p source cutEdge hhead) k n initialLeft initialRight (fun r => decode (r sink))
  intro x
  have h := correct x
  rw [run_glue net p source cutEdge htail hhead hleaf, glue_away] at h
  exact h

end

noncomputable section

open CSL.CircuitProgram CSL.ProgramNetwork

variable {Reg : Type*} [DecidableEq Reg]
variable (program : List (XorGate Reg))

/-- A source starts with its own message. Every gate/pass/sink starts with a
fixed state; the local initialLocalr may encode arbitrary fixed advice. -/
def initialState {k : ℕ}
    (initialLocal : Vertex Reg program.length → (Fin k → Bool) → State)
    (inputs : Reg → Fin k → Bool) : Vertex Reg program.length → State
  | .source r => initialLocal (.source r) (inputs r)
  | v => initialLocal v (fun _ => false)

theorem initial_single_source {k : ℕ}
    (initialLocal : Vertex Reg program.length → (Fin k → Bool) → State)
    (r : Reg) (x : Fin k → Bool) :
    initialState program initialLocal (Function.update (fun _ _ => false) r x) =
      glue (Vertex.source r) (initialLocal (.source r) x)
        (fun v => initialState program initialLocal (fun _ _ => false) v.val) := by
  classical
  funext v
  cases v with
  | source j =>
    by_cases h : j = r
    · subst j
      simp [initialState, glue]
    · simp [initialState, glue, h]
  | gate t => simp [initialState, glue]
  | pass t j => simp [initialState, glue]
  | sink j => simp [initialState, glue]

/-- Every correct (possibly nonlinear, interactive) protocol on the actual
program network sends at most one independent source bit per time slot. -/
theorem program_block_bound {k n : ℕ}
    (p : Protocol (network program) State) (σ : Equiv.Perm Reg)
    (initialLocal : Vertex Reg program.length → (Fin k → Bool) → State)
    (decode : Reg → State → Fin k → Bool)
    (correct : ∀ inputs : Reg → Fin k → Bool, ∀ i,
      decode i (run (network program) p n 0
        (initialState program initialLocal inputs) (.sink (σ i))) = inputs i)
    (r : Reg) : k ≤ n := by
  classical
  let src : Vertex Reg program.length := .source r
  let edge := sourceWire program r
  have ht : (network program).tail edge = src := sourceWire_tail program r
  have hh : (network program).head edge ≠ src := by
    intro h
    have hg := (network program).forward edge
    rw [ht, h] at hg
    exact Nat.lt_irrefl _ hg
  have hl : ∀ e, Incident (network program) e src ↔ e = edge :=
    source_is_leaf program r
  let snk : Away src := ⟨.sink (σ r), by
    change Vertex.sink (σ r) ≠ Vertex.source r
    intro h
    cases h⟩
  apply recovered_bits_le_steps (network program) p src edge ht hh hl k n
    (fun x => initialLocal (.source r) x)
    (fun v => initialState program initialLocal (fun _ _ => false) v.val) snk (decode r)
  intro x
  have h := correct (Function.update (fun _ _ => false) r x) r
  rw [initial_single_source] at h
  simpa only [Function.update_self] using h

/-- Instantiation on the manuscript's literal three-round graph. There is
no linearity restriction on the protocol being bounded. -/
theorem actual_block_bound {d k n : ℕ}
    (p : Protocol (actualNetwork d) State)
    (initialLocal : Vertex (GlobalReg d) (globalProgram d).length → (Fin k → Bool) → State)
    (decode : GlobalReg d → State → Fin k → Bool)
    (correct : ∀ inputs : GlobalReg d → Fin k → Bool, ∀ i,
      decode i (run (actualNetwork d) p n 0
        (initialState (globalProgram d) initialLocal inputs)
        (.sink (globalSwap i))) = inputs i)
    (r : GlobalReg d) : k ≤ n :=
  program_block_bound (globalProgram d) p globalSwap initialLocal decode correct r

end
end CSL.NetworkCut
end NetworkCut

section NetworkRates
/-!
# A single operational definition of coding rates

The existentially quantified code may be nonlinear and interactive. Initial
states are functions only of messages located at that vertex. Correctness
refers to the synchronous physical-edge execution of `NetworkCut`.
The capacity is the supremum of these concrete finite-block rates.
-/

namespace CSL.NetworkRates

open NetworkProtocol

variable {Node Edge Session : Type}
variable (net : RankedNetwork Node Edge) (source sink : Session → Node)

structure BlockCode (k T : ℕ) where
  State : Type
  protocol : NetworkCut.Protocol net State
  initial : (v : Node) → ({i : Session // source i = v} → Fin k → Bool) → State
  decode : Session → State → Fin k → Bool
  correct : ∀ input : Session → Fin k → Bool,
    ∀ i : Session,
      decode i (NetworkCut.run net protocol T 0
        (fun v => initial v (fun j => input j.val)) (sink i)) = input i

def Achievable (rate : ℝ) : Prop :=
  ∃ k T : ℕ, 0 < T ∧ Nonempty (BlockCode net source sink k T) ∧ rate = (k : ℝ) / T

noncomputable def capacity : ℝ := sSup {r : ℝ | Achievable net source sink r}

/-- The zero-rate code uses no shared inputs and no communication information. -/
def zeroCode : BlockCode net source sink 0 1 where
  State := Unit
  protocol := {
    forward := fun _ _ => true
    emit := fun _ _ _ _ => false
    update := fun _ _ _ _ => ()
  }
  initial := fun _ _ => ()
  decode := fun _ _ => Fin.elim0
  correct := by intro input i; funext j; exact Fin.elim0 j

theorem zero_achievable : Achievable net source sink 0 := by
  refine ⟨0,1,by omega,⟨zeroCode net source sink⟩,?_⟩
  norm_num

theorem achievable_nonneg {r : ℝ} (h : Achievable net source sink r) : 0 ≤ r := by
  obtain ⟨k,T,_,_,rfl⟩ := h
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

section CutBound

variable (i₀ : Session) (cutEdge : Edge)
variable (htail : net.tail cutEdge = source i₀)
variable (hhead : net.head cutEdge ≠ source i₀)
variable (hleaf : ∀ e, NetworkCut.Incident net e (source i₀) ↔ e = cutEdge)
variable (hsink : sink i₀ ≠ source i₀)

include htail hhead hleaf hsink

theorem block_bits_le_time {k T : ℕ} (code : BlockCode net source sink k T) : k ≤ T := by
  classical
  let inputs (x : Fin k → Bool) : Session → Fin k → Bool :=
    fun i => if i = i₀ then x else fun _ => false
  let left (x : Fin k → Bool) : code.State :=
    code.initial (source i₀) (fun j => inputs x j.val)
  let right : NetworkCut.Away (source i₀) → code.State :=
    fun v => code.initial v.val (fun _ _ => false)
  have hinit (x : Fin k → Bool) :
      (fun v => code.initial v (fun j => inputs x j.val)) =
      NetworkCut.glue (source i₀) (left x) right := by
    funext v
    by_cases hv : v = source i₀
    · subst v
      simp only [NetworkCut.glue_at_source]
      rfl
    · rw [show NetworkCut.glue (source i₀) (left x) right v = right ⟨v,hv⟩
        from NetworkCut.glue_away (source i₀) (left x) right ⟨v,hv⟩]
      apply congrArg (code.initial v)
      funext j b
      have hj : j.val ≠ i₀ := by
        intro he
        exact hv (j.property.symm.trans (congrArg source he))
      simp [inputs, hj]
  apply NetworkCut.recovered_bits_le_steps net code.protocol (source i₀) cutEdge
    htail hhead hleaf k T left right ⟨sink i₀,hsink⟩ (code.decode i₀)
  intro x
  have hc := code.correct (inputs x) i₀
  rw [hinit] at hc
  simpa [inputs] using hc

theorem achievable_le_one {r : ℝ} (h : Achievable net source sink r) : r ≤ 1 := by
  obtain ⟨k,T,hT,⟨code⟩,rfl⟩ := h
  have hb := block_bits_le_time net source sink i₀ cutEdge htail hhead hleaf hsink code
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  apply (div_le_iff₀ hT').2
  simpa only [one_mul] using (show (k : ℝ) ≤ T by exact_mod_cast hb)

theorem capacity_le_one : capacity net source sink ≤ 1 := by
  apply csSup_le
  · exact ⟨0,zero_achievable net source sink⟩
  · intro r hr
    exact achievable_le_one net source sink i₀ cutEdge htail hhead hleaf hsink hr

end CutBound

/-- When finite operational block codes approach rate one and no operational
code exceeds one, the supremum is exactly one. Both use the SAME rate set. -/
theorem capacity_eq_one
    (upper : ∀ r, Achievable net source sink r → r ≤ 1)
    (near : ∀ r : ℝ, r < 1 → ∃ r', Achievable net source sink r' ∧ r < r') :
    capacity net source sink = 1 := by
  have hne : ({r : ℝ | Achievable net source sink r}).Nonempty :=
    ⟨0,zero_achievable net source sink⟩
  have hbd : BddAbove {r : ℝ | Achievable net source sink r} := ⟨1,upper⟩
  apply le_antisymm
  · exact csSup_le hne (fun r hr => upper r hr)
  · by_contra hn
    have hlt : capacity net source sink < 1 := lt_of_not_ge hn
    obtain ⟨r,hr,hcr⟩ := near _ hlt
    have hrc : r ≤ capacity net source sink := le_csSup hbd hr
    exact (not_lt_of_ge hrc) hcr

theorem exists_pipeline_rate_gt (D : ℕ) (r : ℝ) (hr : r < 1) :
    ∃ k : ℕ, 0 < k ∧ r < (k : ℝ) / (k + D) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max 0 (r * (D : ℝ) / (1-r)))
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkr : r * (D : ℝ) / (1-r) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hden : 0 < 1-r := by linarith
  have hmul := (div_lt_iff₀ hden).1 hkr
  refine ⟨k,by exact_mod_cast hk0,?_⟩
  apply (lt_div_iff₀ (show (0 : ℝ) < k+D by positivity)).2
  nlinarith

/-- All finite pipeline lengths belong to the operational rate set. -/
theorem capacity_eq_one_of_pipeline (D : ℕ)
    (codes : ∀ k, Nonempty (BlockCode net source sink k (k+D)))
    (upper : ∀ r, Achievable net source sink r → r ≤ 1) :
    capacity net source sink = 1 := by
  apply capacity_eq_one net source sink upper
  intro r hr
  obtain ⟨k,hk,hkr⟩ := exists_pipeline_rate_gt D r hr
  refine ⟨(k : ℝ)/(k+D), ?_,hkr⟩
  refine ⟨k,k+D,by omega,codes k,?_⟩
  push_cast
  rfl

section Routing

variable [DecidableEq Edge] [DecidableEq Session]

/-- Standard fractional path-flow routing: a finite family of undirected
walks, with one shared unit-capacity constraint per physical edge. -/
def Routable (rate : ℝ) : Prop :=
  ∃ n : ℕ, ∃ owner : Fin n → Session,
    ∃ walk : ∀ p, GraphRouting.Walk net (source (owner p)) (sink (owner p)),
    ∃ flow : Fin n → ℝ,
      (∀ p, 0 ≤ flow p) ∧
      (∀ e, ∑ p, flow p * ((walk p).edges.count e : ℝ) ≤ 1) ∧
      (∀ i, rate ≤ ∑ p, if owner p = i then flow p else 0)

noncomputable def routingCapacity : ℝ := sSup {r : ℝ | Routable net source sink r}

theorem zero_routable : Routable net source sink 0 := by
  refine ⟨0, Fin.elim0, (fun p => Fin.elim0 p), Fin.elim0, ?_, ?_, ?_⟩
  · intro p; exact Fin.elim0 p
  · intro e; simp
  · intro i; simp

theorem routing_capacity_bound (rho : ℝ)
    (bound : ∀ r, Routable net source sink r → r ≤ rho) :
    routingCapacity net source sink ≤ rho := by
  apply csSup_le
  · exact ⟨0,zero_routable net source sink⟩
  · exact bound

end Routing

end CSL.NetworkRates
end NetworkRates


