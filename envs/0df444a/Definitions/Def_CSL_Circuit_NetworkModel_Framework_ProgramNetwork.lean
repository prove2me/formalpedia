-- Prove2me | Definitions.Def_CSL_Circuit_NetworkModel_Framework_ProgramNetwork
-- name    : CSL_Circuit_NetworkModel_Framework_ProgramNetwork
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:34:10.91975+00:00
-- url     : https://prove2.me/theorems/ab835e1e-a04e-4291-8505-a84f9d2dd868
-- title:
--   Coded sorting library: Circuit / NetworkModel / Framework / ProgramNetwork
-- statement:
--   Module `CodedSorting.Circuit.NetworkModel.Framework.ProgramNetwork` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # The actual finite XOR program as a unit-edge network
--
--   At each program step its true ports meet at one gate vertex. Every other
--   register passes through its own private vertex. These private vertices only
--   subdivide register wires: they never merge different registers. Sources and
--   sinks are separate leaves. Edge `(t,r)` carries the value of register `r`
--   after exactly `t` gates of the literal program.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.NetworkModel.Framework.ProgramNetwork

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_CircuitProgram
import Definitions.Def_CSL_NetworkCoding_Model_NetworkProtocol

/-!
# The actual finite XOR program as a unit-edge network

At each program step its true ports meet at one gate vertex. Every other
register passes through its own private vertex. These private vertices only
subdivide register wires: they never merge different registers. Sources and
sinks are separate leaves. Edge `(t,r)` carries the value of register `r`
after exactly `t` gates of the literal program.
-/

set_option autoImplicit false

namespace CSL.ProgramNetwork

open CSL.Circuit
open CSL.CircuitProgram
open CSL.NetworkProtocol

inductive Vertex (Reg : Type*) (length : ℕ) where
  | source : Reg → Vertex Reg length
  | gate : Fin length → Vertex Reg length
  | pass : Fin length → Reg → Vertex Reg length
  | sink : Reg → Vertex Reg length
  deriving DecidableEq, Fintype

abbrev Wire (Reg : Type*) (length : ℕ) := Fin (length + 1) × Reg

variable {Reg : Type*} [DecidableEq Reg]
variable (program : List (XorGate Reg))

def stageVertex (t : Fin program.length) (r : Reg) : Vertex Reg program.length :=
  if r ∈ (program.get t).ports then .gate t else .pass t r

def vertexRank : Vertex Reg program.length → ℕ
  | .source _ => 0
  | .gate t => t.val + 1
  | .pass t _ => t.val + 1
  | .sink _ => program.length + 1

def wireTail (edge : Wire Reg program.length) : Vertex Reg program.length :=
  if h : edge.1.val = 0 then .source edge.2 else
    stageVertex program ⟨edge.1.val - 1, by have := edge.1.isLt; omega⟩ edge.2

def wireHead (edge : Wire Reg program.length) : Vertex Reg program.length :=
  if h : edge.1.val = program.length then .sink edge.2 else
    stageVertex program ⟨edge.1.val, by have := edge.1.isLt; omega⟩ edge.2

theorem rank_stageVertex (t : Fin program.length) (r : Reg) :
    vertexRank program (stageVertex program t r) = t.val + 1 := by
  unfold stageVertex
  split_ifs <;> rfl

theorem rank_wireTail (edge : Wire Reg program.length) :
    vertexRank program (wireTail program edge) = edge.1.val := by
  unfold wireTail
  split_ifs with h
  · simp [vertexRank, h]
  · rw [rank_stageVertex]
    change edge.1.val - 1 + 1 = edge.1.val
    omega

theorem rank_wireHead (edge : Wire Reg program.length) :
    vertexRank program (wireHead program edge) = edge.1.val + 1 := by
  unfold wireHead
  split_ifs with h
  · simp [vertexRank, h]
  · exact rank_stageVertex program _ _

def network : RankedNetwork (Vertex Reg program.length) (Wire Reg program.length) where
  tail := wireTail program
  head := wireHead program
  rank := vertexRank program
  forward e := by
    rw [rank_wireTail, rank_wireHead]
    omega

def incomingWire (t : Fin program.length) (r : Reg) : Wire Reg program.length :=
  (⟨t.val, Nat.lt_succ_of_lt t.isLt⟩, r)

def outgoingWire (t : Fin program.length) (r : Reg) : Wire Reg program.length :=
  (⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩, r)

def sourceWire (r : Reg) : Wire Reg program.length := (0, r)

def sinkWire (r : Reg) : Wire Reg program.length :=
  (⟨program.length, Nat.lt_succ_self _⟩, r)

theorem incomingWire_head (t : Fin program.length) (r : Reg) :
    wireHead program (incomingWire program t r) = stageVertex program t r := by
  simp [wireHead, incomingWire, Nat.ne_of_lt t.isLt]

theorem outgoingWire_tail (t : Fin program.length) (r : Reg) :
    wireTail program (outgoingWire program t r) = stageVertex program t r := by
  simp [wireTail, outgoingWire]

theorem sourceWire_tail (r : Reg) :
    wireTail program (sourceWire program r) = .source r := by
  simp [wireTail, sourceWire]

theorem sinkWire_head (r : Reg) :
    wireHead program (sinkWire program r) = .sink r := by
  simp [wireHead, sinkWire]

theorem stageVertex_gate (t : Fin program.length) (r : Reg)
    (hr : r ∈ (program.get t).ports) : stageVertex program t r = .gate t := by
  simp only [stageVertex, if_pos hr]

theorem stageVertex_pass (t : Fin program.length) (r : Reg)
    (hr : r ∉ (program.get t).ports) : stageVertex program t r = .pass t r := by
  simp only [stageVertex, if_neg hr]

theorem outgoing_gate_index (t : Fin program.length)
    (edge : Wire Reg program.length) (h : wireTail program edge = .gate t) :
    edge = outgoingWire program t edge.2 := by
  have hr := congrArg (vertexRank program) h
  rw [rank_wireTail] at hr
  apply Prod.ext
  · apply Fin.ext
    exact hr
  · rfl

theorem outgoing_gate_port (t : Fin program.length)
    (edge : Wire Reg program.length) (h : wireTail program edge = .gate t) :
    edge.2 ∈ (program.get t).ports := by
  have he := outgoing_gate_index program t edge h
  rw [he, outgoingWire_tail] at h
  by_contra hn
  rw [stageVertex_pass program t edge.2 hn] at h
  cases h

theorem outgoing_pass_index (t : Fin program.length) (r : Reg)
    (edge : Wire Reg program.length) (h : wireTail program edge = .pass t r) :
    edge = outgoingWire program t r ∧ r ∉ (program.get t).ports := by
  have hrank := congrArg (vertexRank program) h
  rw [rank_wireTail] at hrank
  have he : edge = outgoingWire program t edge.2 := by
    apply Prod.ext
    · apply Fin.ext
      exact hrank
    · rfl
  rw [he, outgoingWire_tail] at h
  by_cases hp : edge.2 ∈ (program.get t).ports
  · rw [stageVertex_gate program t edge.2 hp] at h
    cases h
  · have hreg : edge.2 = r := by
      rw [stageVertex_pass program t edge.2 hp] at h
      injection h
    constructor
    · simpa only [hreg] using he
    · simpa only [hreg] using hp

theorem outgoing_source_index (r : Reg) (edge : Wire Reg program.length)
    (h : wireTail program edge = .source r) : edge = sourceWire program r := by
  have hrank := congrArg (vertexRank program) h
  rw [rank_wireTail] at hrank
  have hz : edge.1.val = 0 := hrank
  have hreg : edge.2 = r := by simpa [wireTail, hz] using h
  apply Prod.ext
  · exact Fin.ext hz
  · exact hreg

theorem no_outgoing_sink (r : Reg) (edge : Wire Reg program.length) :
    wireTail program edge ≠ .sink r := by
  intro h
  have hrank := congrArg (vertexRank program) h
  rw [rank_wireTail] at hrank
  have he := edge.1.isLt
  change edge.1.val = program.length + 1 at hrank
  omega

theorem no_incoming_source (r : Reg) (edge : Wire Reg program.length) :
    wireHead program edge ≠ .source r := by
  intro h
  have hrank := congrArg (vertexRank program) h
  rw [rank_wireHead] at hrank
  change edge.1.val + 1 = 0 at hrank
  omega

theorem incoming_sink_index (r : Reg) (edge : Wire Reg program.length)
    (h : wireHead program edge = .sink r) : edge = sinkWire program r := by
  have hrank := congrArg (vertexRank program) h
  rw [rank_wireHead] at hrank
  have he : edge.1.val = program.length := Nat.add_right_cancel hrank
  have hreg : edge.2 = r := by simpa [wireHead, he] using h
  apply Prod.ext
  · exact Fin.ext he
  · exact hreg

/-- A source has exactly one incident physical edge, hence is a genuine
unit-capacity leaf rather than a symbolic input attached to a gate. -/
theorem source_is_leaf (r : Reg) (edge : Wire Reg program.length) :
    wireTail program edge = .source r ∨ wireHead program edge = .source r ↔
      edge = sourceWire program r := by
  constructor
  · rintro (h | h)
    · exact outgoing_source_index program r edge h
    · exact False.elim (no_incoming_source program r edge h)
  · intro h
    subst edge
    exact Or.inl (sourceWire_tail program r)

theorem sink_is_leaf (r : Reg) (edge : Wire Reg program.length) :
    wireTail program edge = .sink r ∨ wireHead program edge = .sink r ↔
      edge = sinkWire program r := by
  constructor
  · rintro (h | h)
    · exact False.elim (no_outgoing_sink program r edge h)
    · exact incoming_sink_index program r edge h
  · intro h
    subst edge
    exact Or.inr (sinkWire_head program r)

abbrev InputPort (v : Vertex Reg program.length) :=
  {r : Reg // Vertex.source r = v} ⊕
    {edge : Wire Reg program.length // wireHead program edge = v}

abbrev OutputPort (v : Vertex Reg program.length) :=
  {edge : Wire Reg program.length // wireTail program edge = v}

def gateInputMap (t : Fin program.length) :
    (InputPort program (.gate t) → Bit) →ₗ[Bit] (Reg → Bit) :=
  LinearMap.pi (fun r =>
    if hr : r ∈ (program.get t).ports then
      LinearMap.proj (.inr ⟨incomingWire program t r,
        (incomingWire_head program t r).trans (stageVertex_gate program t r hr)⟩)
    else 0)

def localMap : (v : Vertex Reg program.length) →
    (InputPort program v → Bit) →ₗ[Bit] (OutputPort program v → Bit)
  | .source r => LinearMap.pi (fun _ => LinearMap.proj (.inl ⟨r, rfl⟩))
  | .gate t => LinearMap.pi (fun out =>
      (LinearMap.proj out.val.2).comp
        ((program.get t).linearMap.comp (gateInputMap program t)))
  | .pass t r =>
      if hr : r ∈ (program.get t).ports then 0 else
        LinearMap.pi (fun _ => LinearMap.proj (.inr ⟨incomingWire program t r,
          (incomingWire_head program t r).trans (stageVertex_pass program t r hr)⟩))
  | .sink _ => 0

def code (σ : Equiv.Perm Reg) : LinearCode (network program) Reg where
  source := Vertex.source
  sink i := Vertex.sink (σ i)
  localMap := localMap program
  decoder i := LinearMap.proj ⟨sinkWire program (σ i), sinkWire_head program (σ i)⟩

def registerState (input : Reg → Bit) (t : ℕ) : Reg → Bit :=
  runProgram (program.take t) input

theorem registerState_zero (input : Reg → Bit) : registerState program input 0 = input := rfl

theorem registerState_step (input : Reg → Bit) (t : Fin program.length) :
    registerState program input (t.val + 1) =
      (program.get t).eval (registerState program input t.val) := by
  unfold registerState
  rw [List.take_succ_eq_append_getElem t.isLt, runProgram_append]
  rfl

def wireValue (input : Reg → Bit) (edge : Wire Reg program.length) : Bit :=
  registerState program input edge.1.val edge.2

theorem wireValue_source (input : Reg → Bit) (r : Reg) :
    wireValue program input (sourceWire program r) = input r := rfl

theorem wireValue_incoming (input : Reg → Bit) (t : Fin program.length) (r : Reg) :
    wireValue program input (incomingWire program t r) = registerState program input t.val r := rfl

theorem wireValue_outgoing (input : Reg → Bit) (t : Fin program.length) (r : Reg) :
    wireValue program input (outgoingWire program t r) =
      (program.get t).eval (registerState program input t.val) r :=
  congrFun (registerState_step program input t) r

theorem wireValue_sink (input : Reg → Bit) (r : Reg) :
    wireValue program input (sinkWire program r) = runProgram program input r := by
  simp only [wireValue, sinkWire, registerState, List.take_length]

def localInputs (input : Reg → Bit) (v : Vertex Reg program.length) :
    InputPort program v → Bit
  | .inl i => input i.val
  | .inr edge => wireValue program input edge.val

theorem gateInputMap_localInputs (input : Reg → Bit) (t : Fin program.length)
    (r : Reg) (hr : r ∈ (program.get t).ports) :
    gateInputMap program t (localInputs program input (.gate t)) r =
      registerState program input t.val r := by
  simp only [gateInputMap, LinearMap.pi_apply, dif_pos hr, LinearMap.proj_apply,
    localInputs, wireValue_incoming]

/-- Every edge value read from the literal program state satisfies the
local operation at its actual tail vertex, including private pass vertices. -/
theorem localMap_wireValues (input : Reg → Bit) (v : Vertex Reg program.length)
    (out : OutputPort program v) :
    localMap program v (localInputs program input v) out =
      wireValue program input out.val := by
  cases v with
  | source r =>
    change input r = wireValue program input out.val
    rw [outgoing_source_index program r out.val out.property, wireValue_source]
  | gate t =>
    have he := outgoing_gate_index program t out.val out.property
    change (program.get t).eval
      (gateInputMap program t (localInputs program input (.gate t))) out.val.2 = _
    rw [he, wireValue_outgoing]
    apply (program.get t).eval_congr_on_ports
    · intro r hr
      exact gateInputMap_localInputs program input t r hr
    · exact outgoing_gate_port program t out.val out.property
  | pass t r =>
    obtain ⟨he, hr⟩ := outgoing_pass_index program t r out.val out.property
    simp only [localMap, dif_neg hr, LinearMap.pi_apply, LinearMap.proj_apply,
      localInputs]
    rw [he, wireValue_incoming, wireValue_outgoing,
      (program.get t).eval_outside_ports _ r hr]
  | sink r =>
    exact False.elim (no_outgoing_sink program r out.val out.property)

/-- The network's recursively evaluated local linear code exactly matches
the literal register program; no transcript correctness is assumed. -/
theorem network_edgeValue (σ : Equiv.Perm Reg) (input : Reg → Bit)
    (edge : Wire Reg program.length) :
    edgeValue (network program) (code program σ) input edge = wireValue program input edge := by
  apply edgeValue_unique (network program) (code program σ) input
    (wireValue program input)
  intro e
  simp only [code, network]
  rw [← localMap_wireValues program input (wireTail program e) ⟨e, rfl⟩]
  apply congrArg (fun values : InputPort program (wireTail program e) → Bit =>
    localMap program (wireTail program e) values ⟨e, rfl⟩)
  funext port
  cases port <;> rfl

theorem code_correct (σ : Equiv.Perm Reg)
    (hprogram : ∀ input : Reg → Bit,
      runProgram program input = fun r => input (σ.symm r)) :
    Correct (network program) (code program σ) := by
  intro input i
  change edgeValue (network program) (code program σ) input (sinkWire program (σ i)) = input i
  rw [network_edgeValue, wireValue_sink, hprogram]
  simp

theorem depth_bound (edge : Wire Reg program.length) :
    (network program).rank ((network program).tail edge) ≤ program.length := by
  change vertexRank program (wireTail program edge) ≤ program.length
  rw [rank_wireTail]
  exact Nat.le_of_lt_succ edge.1.isLt

/-- The manuscript's actual three-round XOR program, including every dirty
auxiliary register, regarded as a finite unit-edge network. -/
noncomputable def actualNetwork (d : ℕ) := network (globalProgram d)

noncomputable def actualCode (d : ℕ) : LinearCode (actualNetwork d) (GlobalReg d) :=
  code (globalProgram d) globalSwap

/-- All source messages are independent. The actual local code exchanges the
X/Y messages and restores every auxiliary message at its designated sink. -/
theorem actualCode_correct (d : ℕ) : Correct (actualNetwork d) (actualCode d) := by
  apply code_correct
  intro input
  rw [globalProgram_correct]
  funext r
  rcases r with (a | a) | ⟨j,k,(a|i)⟩ <;> rfl

/-- A finite protocol on the actual graph: one bit per physical edge/time,
causal local computation, completion within `k + length(globalProgram d)`
slots, and simultaneous recovery of all independent k-bit messages.

The depth used here is serial program length. The sharper 25-layer schedule
in the manuscript is a separate optimization and is not asserted here. -/
theorem actualFinitePipeline (d k : ℕ) (inputs : Fin k → GlobalReg d → Bit) :
    (∀ e time,
      (Finset.univ.filter (fun batch : Fin k =>
        sendTime (actualNetwork d) batch e = time)).card ≤ 1) ∧
    (∀ (batch : Fin k) e incoming,
      (actualNetwork d).head incoming = (actualNetwork d).tail e →
      sendTime (actualNetwork d) batch incoming < sendTime (actualNetwork d) batch e) ∧
    (∀ (batch : Fin k) e,
      sendTime (actualNetwork d) batch e < k + (globalProgram d).length) ∧
    (∀ (batch : Fin k) i, (actualCode d).decoder i (fun incoming =>
      (packet (actualNetwork d) (actualCode d) inputs incoming.val
        (sendTime (actualNetwork d) batch incoming.val)).getD 0) = inputs batch i) :=
  finite_pipeline (actualNetwork d) (actualCode d) (actualCode_correct d)
    (depth_bound (globalProgram d)) inputs

end CSL.ProgramNetwork


