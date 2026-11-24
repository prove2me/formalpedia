-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveControl
-- name    : CSL_Interchange_Framework_Recursion_RecursiveControl
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:17:56.513197+00:00
-- url     : https://prove2.me/theorems/4ae92e3b-952d-4290-a6d5-ccff1ac01f71
-- title:
--   Coded sorting library: Interchange / Framework / Recursion / RecursiveControl
-- statement:
--   Module `CodedSorting.Interchange.Framework.Recursion.RecursiveControl` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Finite descriptors saved on the physical continuation stack
--
--   The descriptor codec stores every polynomially bounded numeric field and a
--   fixed-program control state. Validity relates an external block disk to a
--   proof-only list of ancestors; that list is not a runtime field.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Recursion.RecursiveControl

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Words_WordConvention
import Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchange
import Definitions.Def_CSL_Interchange_Framework_Recursion_StatefulRecursiveExchange

/-!
# Finite descriptors saved on the physical continuation stack

The descriptor codec stores every polynomially bounded numeric field and a
fixed-program control state. Validity relates an external block disk to a
proof-only list of ancestors; that list is not a runtime field.
-/

set_option autoImplicit false
namespace CSL.RecursiveControl
open WordControl

structure Descriptor (fields N exponent states : ℕ) where
  counters : Fin fields → Fin (N ^ exponent + 1)
  pc : Fin states

variable {fields N exponent states B w : ℕ}

def frameWords (fields exponent states : ℕ) : ℕ :=
  fields*(exponent+1)+Nat.clog 2 (states+1)

def encode (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (descriptor : Descriptor fields N exponent states) :
    Frame (frameWords fields exponent states) w :=
  Fin.append (encodeTuple N w exponent fields hN hw descriptor.counters)
    (encodeConstant w states (word_positive N w hN hw) descriptor.pc.castSucc)

def counterWords (frame : Frame (frameWords fields exponent states) w) (i : Fin fields) :
    Words (exponent+1) w :=
  fun j => frame ((finProdFinEquiv (i,j)).castAdd (Nat.clog 2 (states+1)))

def pcWords (frame : Frame (frameWords fields exponent states) w) :
    Words (Nat.clog 2 (states+1)) w :=
  fun j => frame (j.natAdd (fields*(exponent+1)))

/-- Decoding is total and bounded even for arbitrary disk contents. Valid
saved frames decode without reduction changing any field. -/
def decode (hs : 0 < states) (frame : Frame (frameWords fields exponent states) w) :
    Descriptor fields N exponent states where
  counters i := ⟨decodeWords (counterWords frame i) % (N^exponent+1),Nat.mod_lt _ (by omega)⟩
  pc := ⟨decodeWords (pcWords frame) % states,Nat.mod_lt _ hs⟩

@[simp] theorem decode_encode (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hs : 0 < states)
    (descriptor : Descriptor fields N exponent states) :
    decode hs (encode hN hw descriptor) = descriptor := by
  cases descriptor with
  | mk counters pc =>
    try dsimp only [decode]
    congr 1
    · funext i
      apply Fin.ext
      change decodeWords (counterWords (encode hN hw ⟨counters,pc⟩) i) % (N^exponent+1) = _
      have hc : counterWords (encode hN hw ⟨counters,pc⟩) i =
          fun j => encodeTuple N w exponent fields hN hw counters (finProdFinEquiv (i,j)) := by
        funext j
        simp [counterWords,encode]
      rw [hc,decode_tuple_field,Nat.mod_eq_of_lt (counters i).isLt]
    · apply Fin.ext
      change decodeWords (pcWords (encode hN hw ⟨counters,pc⟩)) % states = _
      have hp : pcWords (encode hN hw ⟨counters,pc⟩) =
          encodeConstant w states (word_positive N w hN hw) pc.castSucc := by
        funext j
        simp [pcWords,encode]
      rw [hp,decode_encodeConstant]
      exact Nat.mod_eq_of_lt pc.isLt

/-- Only disk and one top pointer occur in the runtime state. -/
abbrev State (B w : ℕ) := WordControl.Stack B w

/-- The ghost interpretation of a stack. Earlier frames are below the
block-aligned region of the top frame. -/
def logicalDisk (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) :
    List (Descriptor fields N exponent states) → BlockDisk B w
  | [] => fun _ _ => 0
  | descriptor :: parents => fun address =>
      if parents.length*blocksPerFrame (frameWords fields exponent states) B ≤ address then
        frameBlock B (address-parents.length*blocksPerFrame (frameWords fields exponent states) B)
          (encode hN hw descriptor)
      else logicalDisk hN hw parents address

def Valid (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (frames : List (Descriptor fields N exponent states)) (state : State B w) : Prop :=
  state.top=frames.length ∧
    ∀ address < state.top*blocksPerFrame (frameWords fields exponent states) B,
      state.disk address = logicalDisk hN hw frames address

def enter (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (descriptor : Descriptor fields N exponent states) (state : State B w) :
    StackExecution B w := push (encode hN hw descriptor) state

def leave (hs : 0 < states) (hB : 0 < B) (state : State B w) :
    Option (Descriptor fields N exponent states × StackExecution B w) :=
  (pop (frameWords := frameWords fields exponent states) hB state).map
    (fun result => (decode hs result.1,result.2))

theorem enter_valid (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (descriptor : Descriptor fields N exponent states)
    (frames : List (Descriptor fields N exponent states)) (state : State B w)
    (hv : Valid hN hw frames state) :
    Valid hN hw (descriptor::frames) (enter hN hw descriptor state).state := by
  constructor
  · change state.top+1=(descriptor::frames).length
    simp only [List.length_cons,hv.1]
  · intro address ha
    let t := blocksPerFrame (frameWords fields exponent states) B
    change (push (encode hN hw descriptor) state).state.disk address = _
    by_cases hlow : address < state.top*t
    · rw [push_preserves_parents _ state address hlow,hv.2 address hlow]
      simp only [logicalDisk]
      rw [if_neg (by change ¬ frames.length*t ≤ address; rw [← hv.1]; omega)]
    · have hi : address-state.top*t < t := by
        change address < (state.top+1)*t at ha
        rw [Nat.add_mul,Nat.one_mul] at ha
        omega
      have he : state.top*t+(address-state.top*t)=address := by omega
      change (pushBlocks (encode hN hw descriptor) (state.top*t) t state.disk []).1 address = _
      rw [← he,pushBlocks_at _ _ _ _ _ _ hi]
      rw [he]
      simp only [logicalDisk]
      rw [if_pos (by change frames.length*t ≤ address; rw [← hv.1]; omega)]
      rw [← hv.1]

theorem leave_valid (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hs : 0 < states)
    (hB : 0 < B) (descriptor : Descriptor fields N exponent states)
    (frames : List (Descriptor fields N exponent states)) (state : State B w)
    (hv : Valid hN hw (descriptor::frames) state) :
    ∃ result, leave hs hB state = some (descriptor,result) ∧
      Valid hN hw frames result.state ∧
      result.trace.length = blocksPerFrame (frameWords fields exponent states) B := by
  let F := frameWords fields exponent states
  let t := blocksPerFrame F B
  have htop : state.top=frames.length+1 := by simpa only [List.length_cons] using hv.1
  let restored := popBlocks hB state.disk (frames.length*t) t (fun _ : Fin F => (0 : Word w)) []
  have hframe : restored.1 = encode hN hw descriptor := by
    funext i
    have hi : i.val/B < t :=
      (Nat.div_lt_iff_lt_mul hB).2 (i.isLt.trans_le (frame_fits F B hB))
    rw [show restored.1 i = state.disk (frames.length*t+i.val/B)
      ⟨i.val%B,Nat.mod_lt _ hB⟩ from popBlocks_at hB state.disk _ _ _ _ i hi]
    have ha : frames.length*t+i.val/B < state.top*t := by rw [htop]; nlinarith
    rw [hv.2 _ ha]
    simp only [logicalDisk]
    rw [if_pos (by change frames.length*t ≤ frames.length*t+i.val/B; exact Nat.le_add_right _ _)]
    change frameBlock B (frames.length*t+i.val/B-frames.length*t) (encode hN hw descriptor)
      ⟨i.val%B,Nat.mod_lt _ hB⟩ = _
    rw [Nat.add_sub_cancel_left]
    have he : i.val/B*B+i.val%B=i.val := by simpa only [Nat.mul_comm] using Nat.div_add_mod i.val B
    have hib : i.val < frameWords fields exponent states := i.isLt
    simp only [frameBlock,he,hib,↓reduceDIte,Fin.eta]
  let result : StackExecution B w := ⟨⟨state.disk,frames.length⟩,restored.2⟩
  refine ⟨result,?_,?_,?_⟩
  · unfold leave pop
    rw [if_neg (by omega)]
    simp only [htop,Nat.add_sub_cancel]
    change some (decode hs restored.1,result) = _
    rw [hframe,decode_encode]
  · refine ⟨rfl,?_⟩
    intro address ha
    change state.disk address = _
    have ha' : address < state.top*t := by
      change address < frames.length*t at ha
      rw [htop]
      nlinarith
    rw [hv.2 address ha']
    simp only [logicalDisk]
    rw [if_neg (by change ¬frames.length*t ≤ address; exact Nat.not_le.mpr ha)]
  · simpa only [result,restored,List.length_nil,Nat.zero_add] using
      popBlocks_transfers hB state.disk (frames.length*t) t (fun _ : Fin F => (0 : Word w)) []


/-- Runtime cost history is proof instrumentation. It contains no payload
frames and is excluded from the resident representation. -/
structure Runtime (B w : ℕ) where
  stack : State B w
  trace : List Transfer

def runtimeValid (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (frames : List (Descriptor fields N exponent states)) (runtime : Runtime B w) : Prop :=
  Valid hN hw frames runtime.stack

def enterRuntime (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (descriptor : Descriptor fields N exponent states) (runtime : Runtime B w) : Runtime B w :=
  let result := enter hN hw descriptor runtime.stack
  ⟨result.state,runtime.trace ++ result.trace⟩

def defaultDescriptor (hs : 0 < states) : Descriptor fields N exponent states :=
  ⟨fun _ => 0,⟨0,hs⟩⟩

/-- On a nonempty valid stack the first branch always succeeds. The decoded
on-disk frame is returned to the continuation, rather than discarded. -/
def leaveRuntime (hs : 0 < states) (hB : 0 < B) (runtime : Runtime B w) :
    Descriptor fields N exponent states × Runtime B w :=
  match leave hs hB runtime.stack with
  | none => (defaultDescriptor hs,runtime)
  | some (descriptor,result) => (descriptor,⟨result.state,runtime.trace ++ result.trace⟩)

theorem enterRuntime_valid (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (descriptor : Descriptor fields N exponent states)
    (frames : List (Descriptor fields N exponent states)) (runtime : Runtime B w)
    (hv : runtimeValid hN hw frames runtime) :
    runtimeValid hN hw (descriptor::frames) (enterRuntime hN hw descriptor runtime) :=
  enter_valid hN hw descriptor frames runtime.stack hv

theorem leaveRuntime_valid (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (hs : 0 < states) (hB : 0 < B) (descriptor : Descriptor fields N exponent states)
    (frames : List (Descriptor fields N exponent states)) (runtime : Runtime B w)
    (hv : runtimeValid hN hw (descriptor::frames) runtime) :
    (leaveRuntime (fields := fields) (N := N) (exponent := exponent) hs hB runtime).1 = descriptor ∧
      runtimeValid hN hw frames (leaveRuntime (fields := fields) (N := N) (exponent := exponent) hs hB runtime).2 := by
  obtain ⟨result,hresult,hvalid,_⟩ := leave_valid hN hw hs hB descriptor frames runtime.stack hv
  first
  | exact hvalid
  | (have h_sx := hvalid; simp only [leaveRuntime,hresult,true_and] at h_sx ⊢; exact h_sx)
  | (have h_sx := hvalid; simp only [leaveRuntime,hresult,true_and] at h_sx; exact h_sx)
  | (simp only [leaveRuntime,hresult,true_and]; exact hvalid)

theorem enterRuntime_transfers (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (descriptor : Descriptor fields N exponent states) (runtime : Runtime B w) :
    (enterRuntime hN hw descriptor runtime).trace.length = runtime.trace.length +
      blocksPerFrame (frameWords fields exponent states) B := by
  simp only [enterRuntime,enter,push,List.length_append,pushBlocks_transfers,
    List.length_nil,Nat.zero_add]

theorem leaveRuntime_transfers (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (hs : 0 < states) (hB : 0 < B) (descriptor : Descriptor fields N exponent states)
    (frames : List (Descriptor fields N exponent states)) (runtime : Runtime B w)
    (hv : runtimeValid hN hw (descriptor::frames) runtime) :
    (leaveRuntime (fields := fields) (N := N) (exponent := exponent) hs hB runtime).2.trace.length =
      runtime.trace.length + blocksPerFrame (frameWords fields exponent states) B := by
  obtain ⟨result,hresult,_,hcost⟩ := leave_valid hN hw hs hB descriptor frames runtime.stack hv
  simp only [leaveRuntime,hresult,List.length_append,hcost]

/-- The stack pointer is accounted for separately from the current frame.
Its finite encoding follows once the actual recursion bounds stack depth. -/
def encodedTop (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (runtime : Runtime B w) (htop : runtime.stack.top ≤ N^exponent) : Words (exponent+1) w :=
  encodeCounter N w exponent hN hw ⟨runtime.stack.top,by omega⟩

@[simp] theorem decode_encodedTop (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (runtime : Runtime B w) (htop : runtime.stack.top ≤ N^exponent) :
    decodeWords (encodedTop hN hw runtime htop) = runtime.stack.top :=
  decode_encodeCounter _ _ _ _ _ _

noncomputable def childEnumeration : RecursiveExchange.Child ≃ Fin Parameters.S :=
  Fintype.equivFinOfCardEq RecursiveExchange.child_count

noncomputable def childOf (descriptor : Descriptor fields N exponent Parameters.S) :
    RecursiveExchange.Child := childEnumeration.symm descriptor.pc

noncomputable def boundedDescriptor
    (counters : Fin fields → Fin (N^exponent+1)) (child : RecursiveExchange.Child) :
    Descriptor fields N exponent Parameters.S := ⟨counters,childEnumeration child⟩

@[simp] theorem childOf_boundedDescriptor
    (counters : Fin fields → Fin (N^exponent+1)) (child : RecursiveExchange.Child) :
    childOf (boundedDescriptor counters child) = child := childEnumeration.symm_apply_apply child

/-- Exact three-field construction for the current depth, field width and
file volume. Each proof is required explicitly; no modular truncation is
used to create a descriptor from an unbounded dimension. -/
noncomputable def boundedCallDescriptor (depth width volume : ℕ)
    (hd : depth ≤ N^exponent) (hw : width ≤ N^exponent) (hv : volume ≤ N^exponent)
    (child : RecursiveExchange.Child) : Descriptor 3 N exponent Parameters.S :=
  boundedDescriptor (fun i =>
    if i.val=0 then ⟨depth,by omega⟩ else
    if i.val=1 then ⟨width,by omega⟩ else ⟨volume,by omega⟩) child

@[simp] theorem boundedCallDescriptor_child (depth width volume : ℕ)
    (hd : depth ≤ N^exponent) (hw : width ≤ N^exponent) (hv : volume ≤ N^exponent)
    (child : RecursiveExchange.Child) :
    childOf (boundedCallDescriptor depth width volume hd hw hv child) = child :=
  childOf_boundedDescriptor _ child

/-- The bounded numeric fields have not been discarded: after a physical
save/restore cycle the exact descriptor, including all these fields, returns. -/
theorem restored_counters (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (hs : 0 < states) (hB : 0 < B) (descriptor : Descriptor fields N exponent states)
    (frames : List (Descriptor fields N exponent states)) (runtime : Runtime B w)
    (hv : runtimeValid hN hw (descriptor::frames) runtime) :
    (leaveRuntime (fields := fields) (N := N) (exponent := exponent) hs hB runtime).1.counters = descriptor.counters :=
  congrArg Descriptor.counters (leaveRuntime_valid hN hw hs hB descriptor frames runtime hv).1


theorem child_states_pos : 0 < Parameters.S := by norm_num [Parameters.S_value]

/-- Concrete instantiation of the stateful data interpreter's control
interface. Enter and leave are the physical write/read procedures above. -/
noncomputable def physicalControl (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B) :
    StatefulRecursiveExchange.Control (Runtime B w) (Descriptor fields N exponent Parameters.S) where
  childOf := childOf
  enter := enterRuntime hN hw
  leave := leaveRuntime child_states_pos hB
  Valid := runtimeValid hN hw
  enter_valid := enterRuntime_valid hN hw
  leave_valid := leaveRuntime_valid hN hw child_states_pos hB

/-- This theorem runs the real state-threaded payload interpreter with the
physical stack instance; it is not a separate traversal of a resource tree.
The descriptor builder is exposed, together with its exact child identity. -/
theorem physical_run_correct (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (makeFrame : ℕ → ℕ → ℕ → RecursiveExchange.Child → Descriptor fields N exponent Parameters.S)
    (hframe : ∀ depth width volume c, childOf (makeFrame depth width volume c) = c)
    (baseWidth cutoff k rows : ℕ) {Prefix Gap Suffix : Type}
    [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W^k))
    (F : Address.FullAddress Prefix (RecursiveExchange.Scalar (baseWidth*Parameters.m^k)) Gap Suffix →
      Circuit.Bit)
    (frames : List (Descriptor fields N exponent Parameters.S)) (runtime : Runtime B w)
    (hv : runtimeValid hN hw frames runtime) :
    (StatefulRecursiveExchange.run (physicalControl hN hw hB) makeFrame
      baseWidth cutoff k rows layout F runtime).1 = Address.transport Address.exchangeEquiv F ∧
      runtimeValid hN hw frames (StatefulRecursiveExchange.run (physicalControl hN hw hB)
        makeFrame baseWidth cutoff k rows layout F runtime).2 :=
  StatefulRecursiveExchange.run_correct (physicalControl hN hw hB) makeFrame hframe
    baseWidth cutoff k rows layout F frames runtime hv

/-- The transfer count of an actual framed data call includes the push and
pop performed around its child. The child's own transfers remain explicit. -/
theorem framed_child_transfers {Addr : Type} (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (hB : 0 < B) (descriptor : Descriptor fields N exponent Parameters.S)
    (op : (Addr → Circuit.Bit) → Runtime B w → (Addr → Circuit.Bit) × Runtime B w)
    (frames : List (Descriptor fields N exponent Parameters.S))
    (hop : ∀ F runtime, runtimeValid hN hw (descriptor::frames) runtime →
      runtimeValid hN hw (descriptor::frames) (op F runtime).2)
    (F : Addr → Circuit.Bit) (runtime : Runtime B w)
    (hv : runtimeValid hN hw frames runtime) :
    (StatefulRecursiveExchange.framedChild (physicalControl hN hw hB) descriptor op F runtime).2.trace.length =
      (op F (enterRuntime hN hw descriptor runtime)).2.trace.length +
        blocksPerFrame (frameWords fields exponent Parameters.S) B := by
  have hentered := enterRuntime_valid hN hw descriptor frames runtime hv
  have hreturned := hop F (enterRuntime hN hw descriptor runtime) hentered
  exact leaveRuntime_transfers hN hw child_states_pos hB descriptor frames
    (op F (enterRuntime hN hw descriptor runtime)).2 hreturned

/-- If the child increments the actual transfer trace by childCost, its
surrounding save and restore add exactly two frame-block counts. -/
theorem framed_child_transfer_increment {Addr : Type} (hN : 2 ≤ N)
    (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (descriptor : Descriptor fields N exponent Parameters.S)
    (op : (Addr → Circuit.Bit) → Runtime B w → (Addr → Circuit.Bit) × Runtime B w)
    (frames : List (Descriptor fields N exponent Parameters.S)) (childCost : ℕ)
    (hop : ∀ F runtime, runtimeValid hN hw (descriptor::frames) runtime →
      runtimeValid hN hw (descriptor::frames) (op F runtime).2 ∧
        (op F runtime).2.trace.length = runtime.trace.length+childCost)
    (F : Addr → Circuit.Bit) (runtime : Runtime B w)
    (hv : runtimeValid hN hw frames runtime) :
    (StatefulRecursiveExchange.framedChild (physicalControl hN hw hB) descriptor op F runtime).2.trace.length =
      runtime.trace.length+childCost+2*blocksPerFrame (frameWords fields exponent Parameters.S) B := by
  rw [framed_child_transfers hN hw hB descriptor op frames (fun F st h => (hop F st h).1) F runtime hv]
  have hentered := enterRuntime_valid hN hw descriptor frames runtime hv
  rw [(hop F (enterRuntime hN hw descriptor runtime) hentered).2,enterRuntime_transfers]
  omega

/-- A total descriptor builder has an explicit out-of-range branch. The
theorem below shows that bounded actual executions cannot observe it. -/
noncomputable def checkedCallDescriptor
    (fallback : ℕ → ℕ → ℕ → RecursiveExchange.Child → Descriptor 3 N exponent Parameters.S)
    (depth width volume : ℕ) (child : RecursiveExchange.Child) :
    Descriptor 3 N exponent Parameters.S :=
  if h : depth ≤ N^exponent ∧ width ≤ N^exponent ∧ volume ≤ N^exponent then
    boundedCallDescriptor depth width volume h.1 h.2.1 h.2.2 child
  else fallback depth width volume child

@[simp] theorem checkedCallDescriptor_in_range
    (fallback : ℕ → ℕ → ℕ → RecursiveExchange.Child → Descriptor 3 N exponent Parameters.S)
    (depth width volume : ℕ) (child : RecursiveExchange.Child)
    (hd : depth ≤ N^exponent) (hw : width ≤ N^exponent) (hv : volume ≤ N^exponent) :
    checkedCallDescriptor fallback depth width volume child =
      boundedCallDescriptor depth width volume hd hw hv child := by
  have h : depth ≤ N^exponent ∧ width ≤ N^exponent ∧ volume ≤ N^exponent := ⟨hd,hw,hv⟩
  simp only [checkedCallDescriptor,dif_pos h]

theorem checkedCallDescriptor_exact
    (fallback : ℕ → ℕ → ℕ → RecursiveExchange.Child → Descriptor 3 N exponent Parameters.S)
    (depth width volume : ℕ) (child : RecursiveExchange.Child)
    (hd : depth ≤ N^exponent) (hw : width ≤ N^exponent) (hv : volume ≤ N^exponent) :
    let d := checkedCallDescriptor fallback depth width volume child
    (d.counters 0).val=depth ∧ (d.counters 1).val=width ∧
      (d.counters 2).val=volume ∧ childOf d=child := by
  simp [checkedCallDescriptor_in_range fallback depth width volume child hd hw hv,
    boundedCallDescriptor,boundedDescriptor,childOf,childEnumeration]

/-- All fallback branches give the same complete payload and physical-stack
execution when the root dimensions satisfy the global polynomial bound.
The imported congruence theorem follows the real nested callbacks and their
proved complete-address child volumes. -/
theorem checked_run_fallback_independent
    (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (fallback₁ fallback₂ : ℕ → ℕ → ℕ → RecursiveExchange.Child → Descriptor 3 N exponent Parameters.S)
    (baseWidth cutoff k rows : ℕ) {Prefix Gap Suffix : Type}
    [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W^k))
    (hk : k ≤ N^exponent) (hwidth : baseWidth*Parameters.m^k ≤ N^exponent)
    (hvolume : Fintype.card (Address.FullAddress Prefix
      (RecursiveExchange.Scalar (baseWidth*Parameters.m^k)) Gap Suffix) ≤ N^exponent)
    (F : Address.FullAddress Prefix (RecursiveExchange.Scalar (baseWidth*Parameters.m^k)) Gap Suffix →
      Circuit.Bit) (runtime : Runtime B w) :
    StatefulRecursiveExchange.run (physicalControl hN hw hB) (checkedCallDescriptor fallback₁)
      baseWidth cutoff k rows layout F runtime =
    StatefulRecursiveExchange.run (physicalControl hN hw hB) (checkedCallDescriptor fallback₂)
      baseWidth cutoff k rows layout F runtime := by
  apply StatefulRecursiveExchange.run_congr_frames
  intro depth width volume c hd hwidth' hvolume'
  rw [checkedCallDescriptor_in_range fallback₁ depth width volume c
      (hd.trans hk) (hwidth'.trans hwidth) (hvolume'.trans hvolume),
    checkedCallDescriptor_in_range fallback₂ depth width volume c
      (hd.trans hk) (hwidth'.trans hwidth) (hvolume'.trans hvolume)]

noncomputable def callDescriptor : ℕ → ℕ → ℕ → RecursiveExchange.Child →
    Descriptor 3 N exponent Parameters.S :=
  checkedCallDescriptor (fun _ _ _ child => boundedDescriptor (fun _ => 0) child)

@[simp] theorem callDescriptor_child (depth width volume : ℕ) (child : RecursiveExchange.Child) :
    childOf (callDescriptor (N := N) (exponent := exponent) depth width volume child) = child := by
  unfold callDescriptor checkedCallDescriptor
  split <;> simp

/-- Closed physical-control instantiation of the payload correctness theorem.
The separate range theorem is needed to conclude exact numeric recording. -/
theorem call_run_correct (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (baseWidth cutoff k rows : ℕ) {Prefix Gap Suffix : Type}
    [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W^k))
    (F : Address.FullAddress Prefix (RecursiveExchange.Scalar (baseWidth*Parameters.m^k)) Gap Suffix →
      Circuit.Bit)
    (frames : List (Descriptor 3 N exponent Parameters.S)) (runtime : Runtime B w)
    (hv : runtimeValid hN hw frames runtime) :
    (StatefulRecursiveExchange.run (physicalControl hN hw hB) (callDescriptor (exponent := exponent))
      baseWidth cutoff k rows layout F runtime).1 = Address.transport Address.exchangeEquiv F ∧
      runtimeValid hN hw frames (StatefulRecursiveExchange.run (physicalControl hN hw hB)
        (callDescriptor (exponent := exponent)) baseWidth cutoff k rows layout F runtime).2 :=
  physical_run_correct hN hw hB callDescriptor callDescriptor_child
    baseWidth cutoff k rows layout F frames runtime hv

end CSL.RecursiveControl


