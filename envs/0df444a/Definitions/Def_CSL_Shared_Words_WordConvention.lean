-- Prove2me | Definitions.Def_CSL_Shared_Words_WordConvention
-- name    : CSL_Shared_Words_WordConvention
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:39:26.026267+00:00
-- url     : https://prove2.me/theorems/3637fcc5-d720-409b-a9b9-cb193cbf1940
-- title:
--   Coded sorting library: Shared / Words / WordConvention
-- statement:
--   Module `CodedSorting.Shared.Words.WordConvention` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Bounded global-word control and an external frame stack
--
--   A Lean natural number is not a machine word. Counter encodings below require
--   an explicit polynomial bound and the global word-size bound. Completed stack
--   frames live in an addressed block disk; the active frame and one block buffer
--   are the only payload residents of a stack operation.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Words.WordConvention

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Fields_FieldPacking
import Definitions.Def_CSL_Circuit_Framework_TriangularProgramBounds
import Mathlib.Data.Nat.Log

section WordControl
/-!
# Bounded global-word control and an external frame stack

A Lean natural number is not a machine word. Counter encodings below require
an explicit polynomial bound and the global word-size bound. Completed stack
frames live in an addressed block disk; the active frame and one block buffer
are the only payload residents of a stack operation.
-/

set_option autoImplicit false
namespace CSL.WordControl

abbrev Word (w : ℕ) := Fin (2 ^ w)
abbrev Words (count w : ℕ) := Fin count → Word w

/-- Integer form of w≥ceil(log₂ N), with the word size fixed globally. -/
theorem global_word_capacity (N w : ℕ) (hw : Nat.clog 2 N ≤ w) : N ≤ 2 ^ w :=
  (Nat.le_pow_iff_clog_le (by omega)).2 hw

/-- An inclusive bound N^c requires c+1 words, including the endpoint when
N itself is an exact power of two. The number of words is independent of N. -/
theorem polynomial_counter_capacity (N w c : ℕ) (hN : 2 ≤ N)
    (hw : Nat.clog 2 N ≤ w) : N ^ c + 1 ≤ (2 ^ w) ^ (c+1) := by
  have hp : 0 < N ^ c := pow_pos (by omega) _
  have hstep : N ^ c + 1 ≤ N ^ (c+1) := by
    rw [pow_succ]
    nlinarith
  exact hstep.trans (Nat.pow_le_pow_left (global_word_capacity N w hw) (c+1))

def encodeCounter (N w c : ℕ) (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (x : Fin (N ^ c + 1)) : Words (c+1) w :=
  finFunctionFinEquiv.symm (x.castLE (polynomial_counter_capacity N w c hN hw))

def decodeWords {count w : ℕ} (words : Words count w) : ℕ :=
  (finFunctionFinEquiv words).val

@[simp] theorem decode_encodeCounter (N w c : ℕ) (hN : 2 ≤ N)
    (hw : Nat.clog 2 N ≤ w) (x : Fin (N ^ c + 1)) :
    decodeWords (encodeCounter N w c hN hw x) = x.val := by
  simp only [decodeWords,encodeCounter,Equiv.apply_symm_apply,Fin.coe_castLE]

theorem encodeCounter_injective (N w c : ℕ) (hN : 2 ≤ N)
    (hw : Nat.clog 2 N ≤ w) : Function.Injective (encodeCounter N w c hN hw) := by
  intro x y he
  apply Fin.ext
  simpa only [decode_encodeCounter] using congrArg decodeWords he

/-- A fixed tuple of polynomially bounded counters has a fixed word count.
This is a concrete array of words, not a cardinality-only existence claim. -/
def encodeTuple (N w c fields : ℕ) (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (frame : Fin fields → Fin (N ^ c + 1)) : Words (fields*(c+1)) w :=
  fun i => encodeCounter N w c hN hw (frame (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2

theorem encodeTuple_injective (N w c fields : ℕ) (hN : 2 ≤ N)
    (hw : Nat.clog 2 N ≤ w) : Function.Injective (encodeTuple N w c fields hN hw) := by
  intro x y he
  funext i
  apply encodeCounter_injective N w c hN hw
  funext j
  have h := congrFun he (finProdFinEquiv (i,j))
  simpa only [encodeTuple,Equiv.symm_apply_apply] using h

/-- The actual stream loops' two public counters are covered without
silently changing their type from an unbounded Nat to a single word. -/
def streamCounters (N c Q remaining offset : ℕ) (hQ : Q ≤ N ^ c)
    (h : offset+remaining ≤ Q) : Fin 2 → Fin (N ^ c+1) :=
  fun i => if i.val = 0 then ⟨remaining,by omega⟩ else ⟨offset,by omega⟩

theorem stream_counter_words (N w c Q remaining offset : ℕ)
    (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hQ : Q ≤ N ^ c)
    (h : offset+remaining ≤ Q) :
    ∃ words : Words (2*(c+1)) w,
      words = encodeTuple N w c 2 hN hw (streamCounters N c Q remaining offset hQ h) :=
  ⟨_,rfl⟩

/-- Per-bucket control is not omitted: d counters per bucket require
K*d*(c+1) words. With B≥1 this is absorbed by a constant multiple of K*B. -/
theorem bucket_metadata_absorbed (K fields c B : ℕ) (hB : 0 < B) :
    (K*B) + K*fields*(c+1) ≤ (1+fields*(c+1))*(K*B) := by
  have h : K*fields*(c+1) ≤ (K*fields*(c+1))*B := Nat.le_mul_of_pos_right _ hB
  nlinarith

abbrev Frame (frameWords w : ℕ) := Words frameWords w

def blocksPerFrame (frameWords B : ℕ) := (frameWords+B-1)/B

/-- The disk is block addressed. Every block contains exactly B global words. -/
abbrev BlockDisk (B w : ℕ) := ℕ → Fin B → Word w

inductive Transfer where
  | read (block : ℕ)
  | write (block : ℕ)
  deriving DecidableEq

/-- trace is ghost history; disk is external storage. Only top is resident
control, and it will be encoded using an explicit polynomial-space bound. -/
structure Stack (B w : ℕ) where
  disk : BlockDisk B w
  top : ℕ

structure StackExecution (B w : ℕ) where
  state : Stack B w
  trace : List Transfer

/-- Build one transfer buffer from the active frame, zero-padding only the
last block. The complete vector frame is the active, constant-size frame. -/
def frameBlock {frameWords w : ℕ} (B block : ℕ) (frame : Frame frameWords w) :
    Fin B → Word w := fun j =>
  if h : block*B+j.val < frameWords then frame ⟨block*B+j.val,h⟩ else 0

def writeBlock {B w : ℕ} (disk : BlockDisk B w) (address : ℕ)
    (buffer : Fin B → Word w) : BlockDisk B w :=
  fun a => if a = address then buffer else disk a

def pushBlocks {frameWords B w : ℕ} (frame : Frame frameWords w) (base : ℕ) :
    ℕ → BlockDisk B w → List Transfer → BlockDisk B w × List Transfer
  | 0, disk, trace => (disk,trace)
  | n+1, disk, trace =>
      pushBlocks frame base n (writeBlock disk (base+n) (frameBlock B n frame))
        (trace ++ [.write (base+n)])

/-- A push writes each block of one frame exactly once. Existing frames are
left on disk and do not appear as an in-memory stack list. -/
def push {frameWords B w : ℕ} (frame : Frame frameWords w) (stack : Stack B w) :
    StackExecution B w :=
  let result := pushBlocks frame (stack.top*blocksPerFrame frameWords B)
    (blocksPerFrame frameWords B) stack.disk []
  ⟨⟨result.1,stack.top+1⟩,result.2⟩

/-- Restore the words belonging to one physically read block. The update
consults only the block buffer, not the external disk. -/
def loadFrameBlock {frameWords B w : ℕ} (hB : 0 < B) (block : ℕ)
    (buffer : Fin B → Word w) (frame : Frame frameWords w) : Frame frameWords w :=
  fun i => if i.val/B = block then buffer ⟨i.val%B,Nat.mod_lt _ hB⟩ else frame i

def popBlocks {frameWords B w : ℕ} (hB : 0 < B) (disk : BlockDisk B w) (base : ℕ) :
    ℕ → Frame frameWords w → List Transfer → Frame frameWords w × List Transfer
  | 0, frame, trace => (frame,trace)
  | n+1, frame, trace =>
      let buffer := disk (base+n)
      popBlocks hB disk base n (loadFrameBlock hB n buffer frame)
        (trace ++ [.read (base+n)])

/-- A pop restores only one frame. The old parent stack remains external. -/
def pop {frameWords B w : ℕ} (hB : 0 < B) (stack : Stack B w) :
    Option (Frame frameWords w × StackExecution B w) :=
  if stack.top = 0 then none else
    let result := popBlocks hB stack.disk ((stack.top-1)*blocksPerFrame frameWords B)
      (blocksPerFrame frameWords B) (fun _ => 0) []
    some (result.1,⟨⟨stack.disk,stack.top-1⟩,result.2⟩)

theorem blocksPerFrame_bound (frameWords B : ℕ) (hB : 0 < B) :
    blocksPerFrame frameWords B ≤ 1+frameWords/B := by
  have h : (frameWords+B-1)/B ≤ (frameWords+B)/B :=
    Nat.div_le_div_right (show frameWords+B-1 ≤ frameWords+B by omega)
  simpa only [blocksPerFrame,Nat.add_div_right _ hB,Nat.add_comm] using h

theorem frame_fits (frameWords B : ℕ) (hB : 0 < B) :
    frameWords ≤ blocksPerFrame frameWords B * B := by
  have hm := Nat.mod_lt (frameWords+B-1) hB
  have hd := Nat.mod_add_div (frameWords+B-1) B
  unfold blocksPerFrame
  rw [Nat.mul_comm]
  omega

theorem pushBlocks_transfers {frameWords B w : ℕ} (frame : Frame frameWords w)
    (base n : ℕ) (disk : BlockDisk B w) (trace : List Transfer) :
    (pushBlocks frame base n disk trace).2.length = trace.length+n := by
  induction n generalizing disk trace with
  | zero => rfl
  | succ n ih => simp only [pushBlocks,ih,List.length_append,List.length_singleton]; omega

theorem popBlocks_transfers {frameWords B w : ℕ} (hB : 0 < B)
    (disk : BlockDisk B w) (base n : ℕ) (frame : Frame frameWords w) (trace : List Transfer) :
    (popBlocks hB disk base n frame trace).2.length = trace.length+n := by
  induction n generalizing frame trace with
  | zero => rfl
  | succ n ih => simp only [popBlocks,ih,List.length_append,List.length_singleton]; omega

theorem pushBlocks_outside {frameWords B w : ℕ} (frame : Frame frameWords w)
    (base n : ℕ) (disk : BlockDisk B w) (trace : List Transfer) (address : ℕ)
    (h : address < base ∨ base+n ≤ address) :
    (pushBlocks frame base n disk trace).1 address = disk address := by
  induction n generalizing disk trace with
  | zero => rfl
  | succ n ih =>
    rw [pushBlocks,ih _ _ (by omega)]
    simp only [writeBlock,if_neg (show address ≠ base+n by omega)]

theorem pushBlocks_at {frameWords B w : ℕ} (frame : Frame frameWords w)
    (base n : ℕ) (disk : BlockDisk B w) (trace : List Transfer) (i : ℕ) (hi : i < n) :
    (pushBlocks frame base n disk trace).1 (base+i) = frameBlock B i frame := by
  induction n generalizing disk trace with
  | zero => omega
  | succ n ih =>
    rw [pushBlocks]
    by_cases h : i < n
    · exact ih _ _ h
    · have he : i=n := by omega
      subst i
      rw [pushBlocks_outside frame base n _ _ (base+n) (Or.inr le_rfl)]
      simp only [writeBlock,↓reduceIte]

theorem popBlocks_outside {frameWords B w : ℕ} (hB : 0 < B)
    (disk : BlockDisk B w) (base n : ℕ) (frame : Frame frameWords w)
    (trace : List Transfer) (i : Fin frameWords) (hi : n ≤ i.val/B) :
    (popBlocks hB disk base n frame trace).1 i = frame i := by
  induction n generalizing frame trace with
  | zero => rfl
  | succ n ih =>
    rw [popBlocks,ih _ _ (by omega)]
    simp only [loadFrameBlock,if_neg (show i.val/B ≠ n by omega)]

theorem popBlocks_at {frameWords B w : ℕ} (hB : 0 < B)
    (disk : BlockDisk B w) (base n : ℕ) (frame : Frame frameWords w)
    (trace : List Transfer) (i : Fin frameWords) (hi : i.val/B < n) :
    (popBlocks hB disk base n frame trace).1 i =
      disk (base+i.val/B) ⟨i.val%B,Nat.mod_lt _ hB⟩ := by
  induction n generalizing frame trace with
  | zero => exact (Nat.not_lt_zero _ hi).elim
  | succ n ih =>
    rw [popBlocks]
    by_cases h : i.val/B < n
    · exact ih _ _ h
    · have he : i.val/B=n := by omega
      rw [popBlocks_outside hB disk base n _ _ i (by omega)]
      simp only [loadFrameBlock,he,↓reduceIte]

theorem push_preserves_parents {frameWords B w : ℕ} (frame : Frame frameWords w)
    (stack : Stack B w) (address : ℕ) (h : address < stack.top*blocksPerFrame frameWords B) :
    (push frame stack).state.disk address = stack.disk address :=
  pushBlocks_outside frame _ _ _ _ address (Or.inl h)

/-- A pushed frame is read back exactly, using one actual read per stored
frame block. Removing it changes only the top pointer; all parents remain
external and retain their words. -/
theorem pop_push {frameWords B w : ℕ} (hB : 0 < B)
    (frame : Frame frameWords w) (stack : Stack B w) :
    ∃ result,
      pop (frameWords := frameWords) hB (push frame stack).state = some (frame,result) ∧
      result.state.top = stack.top ∧
      (∀ address < stack.top*blocksPerFrame frameWords B,
        result.state.disk address = stack.disk address) ∧
      (push frame stack).trace.length = blocksPerFrame frameWords B ∧
      result.trace.length = blocksPerFrame frameWords B := by
  let disk := (push frame stack).state.disk
  let restored := popBlocks hB disk (stack.top*blocksPerFrame frameWords B)
    (blocksPerFrame frameWords B) (fun _ : Fin frameWords => (0 : Word w)) []
  have hframe : restored.1 = frame := by
    funext i
    have hi : i.val/B < blocksPerFrame frameWords B :=
      (Nat.div_lt_iff_lt_mul hB).2 (i.isLt.trans_le (frame_fits frameWords B hB))
    rw [show restored.1 i = disk (stack.top*blocksPerFrame frameWords B+i.val/B)
      ⟨i.val%B,Nat.mod_lt _ hB⟩ from popBlocks_at hB disk _ _ _ _ i hi]
    change (pushBlocks frame _ _ stack.disk []).1 _ _ = _
    rw [pushBlocks_at frame _ _ _ _ _ hi]
    have he : i.val/B*B+i.val%B = i.val := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod i.val B
    simp only [frameBlock,he,Fin.eta,i.isLt,↓reduceDIte]
  let result : StackExecution B w := ⟨⟨disk,stack.top⟩,restored.2⟩
  refine ⟨result,?_,rfl,?_,?_,?_⟩
  · change (if stack.top+1=0 then _ else _) = _
    rw [if_neg (by omega)]
    simp only [Nat.add_sub_cancel]
    change some (restored.1,result) = _
    rw [hframe]
  · intro address ha
    exact push_preserves_parents frame stack address ha
  · simpa only [push,List.length_nil,Nat.zero_add] using
      pushBlocks_transfers frame (stack.top*blocksPerFrame frameWords B)
        (blocksPerFrame frameWords B) stack.disk []
  · simpa only [result,restored,List.length_nil,Nat.zero_add] using
      popBlocks_transfers hB disk (stack.top*blocksPerFrame frameWords B)
        (blocksPerFrame frameWords B) (fun _ : Fin frameWords => (0 : Word w)) []

theorem push_transfer_bound {frameWords B w : ℕ} (hB : 0 < B)
    (frame : Frame frameWords w) (stack : Stack B w) :
    (push frame stack).trace.length ≤ 1+frameWords/B := by
  have h := pushBlocks_transfers frame (stack.top*blocksPerFrame frameWords B)
    (blocksPerFrame frameWords B) stack.disk []
  have he : (push frame stack).trace.length = blocksPerFrame frameWords B := by first
    | exact h
    | (have h_sx := h; simp  at h_sx ⊢; exact h_sx)
    | (have h_sx := h; simp  at h_sx; exact h_sx)
    | (simp ; exact h)
  rw [he]
  exact blocksPerFrame_bound frameWords B hB

/-- Neither push nor pop stores all ancestors in RAM: the resident payload
types have one current frame and one block buffer, independent of stack.top. -/
abbrev StackResident (frameWords B w : ℕ) := Frame frameWords w × (Fin B → Word w)

theorem stack_resident_word_count (frameWords B : ℕ) :
    Fintype.card (Fin frameWords ⊕ Fin B) = frameWords+B := by simp


/-- Fixed circuit and program counters also occupy a fixed word count,
even when the input is too small to fit a fixed constant in one word. -/
def encodeConstant (w bound : ℕ) (hw : 1 ≤ w) (x : Fin (bound+1)) :
    Words (Nat.clog 2 (bound+1)) w :=
  finFunctionFinEquiv.symm (x.castLE (by
    have hbase : 2 ≤ 2^w := by
      simpa using (Nat.pow_le_pow_right (by omega : 0 < 2) hw)
    exact (Nat.le_pow_clog (by omega : 1 < 2) (bound+1)).trans
      (Nat.pow_le_pow_left hbase _)))

@[simp] theorem decode_encodeConstant (w bound : ℕ) (hw : 1 ≤ w) (x : Fin (bound+1)) :
    decodeWords (encodeConstant w bound hw x) = x.val := by
  simp only [decodeWords,encodeConstant,Equiv.apply_symm_apply,Fin.coe_castLE]

theorem word_positive (N w : ℕ) (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) : 1 ≤ w := by
  have h := global_word_capacity N w hw
  by_contra hn
  have hz : w=0 := by omega
  simp only [hz,pow_zero] at h
  omega

def programCounterWords {Pass : Type*} (m w : ℕ) (hw : 1 ≤ w)
    (ps : List Pass) (hps : ps.length ≤ 12*m) (pc : Fin (ps.length+1)) :
    Words (Nat.clog 2 (12*m+1)) w :=
  encodeConstant w (12*m) hw (pc.castLE (by omega))

@[simp] theorem decode_programCounterWords {Pass : Type*} (m w : ℕ) (hw : 1 ≤ w)
    (ps : List Pass) (hps : ps.length ≤ 12*m) (pc : Fin (ps.length+1)) :
    decodeWords (programCounterWords m w hw ps hps pc) = pc.val := by
  simp only [programCounterWords,decode_encodeConstant,Fin.coe_castLE]

theorem successor_power_bound (N c : ℕ) (hN : 2 ≤ N) : N^c+1 ≤ N^(c+1) := by
  have hp : 0 < N^c := pow_pos (by omega) _
  rw [pow_succ]
  nlinarith

/-- Addresses used by a frame operation are polynomially bounded whenever
the stack height and frame length are. This includes block-alignment gaps. -/
theorem stack_block_address_bound (N top frameWords B a b block : ℕ)
    (hN : 2 ≤ N) (hB : 0 < B) (htop : top ≤ N^a) (hframe : frameWords ≤ N^b)
    (hblock : block < blocksPerFrame frameWords B) :
    top*blocksPerFrame frameWords B+block < N^(a+b+2) := by
  have hb : blocksPerFrame frameWords B ≤ frameWords+1 := by
    have h := blocksPerFrame_bound frameWords B hB
    have hd := Nat.div_le_self frameWords B
    omega
  have ht : top+1 ≤ N^(a+1) := (Nat.add_le_add_right htop 1).trans
    (successor_power_bound N a hN)
  have hf : blocksPerFrame frameWords B ≤ N^(b+1) :=
    hb.trans ((Nat.add_le_add_right hframe 1).trans (successor_power_bound N b hN))
  have hmul := Nat.mul_le_mul ht hf
  have hi : top*blocksPerFrame frameWords B+block <
      (top+1)*blocksPerFrame frameWords B := by nlinarith
  apply hi.trans_le
  calc
    (top+1)*blocksPerFrame frameWords B ≤ N^(a+1)*N^(b+1) := hmul
    _ = N^(a+b+2) := by rw [← pow_add]; congr 1; omega

theorem stack_space_bound (top frameWords B : ℕ) :
    top*blocksPerFrame frameWords B*B ≤ top*(frameWords+B) := by
  have h := Nat.div_mul_le_self (frameWords+B-1) B
  have hh : blocksPerFrame frameWords B*B ≤ frameWords+B := by
    unfold blocksPerFrame
    omega
  nlinarith

/-- Two nonnegative operands with polynomial bounds have polynomially
bounded intermediate addition and multiplication, with fixed exponents. -/
theorem arithmetic_counter_bounds (N c x y : ℕ) (hN : 2 ≤ N)
    (hx : x ≤ N^c) (hy : y ≤ N^c) :
    x+y ≤ N^(c+1) ∧ x*y ≤ N^(2*c) ∧ x/y ≤ N^c ∧ x%y ≤ N^c := by
  refine ⟨?_,?_,(Nat.div_le_self x y).trans hx,(Nat.mod_le x y).trans hx⟩
  · rw [pow_succ]
    nlinarith
  · have h := Nat.mul_le_mul hx hy
    simpa only [two_mul,pow_add] using h


/-- Decoding a field of the concrete contiguous word tuple recovers the
original counter, so the tuple encoding is usable by a real controller. -/
theorem decode_tuple_field (N w c fields : ℕ) (hN : 2 ≤ N)
    (hw : Nat.clog 2 N ≤ w) (frame : Fin fields → Fin (N^c+1)) (i : Fin fields) :
    decodeWords (fun j => encodeTuple N w c fields hN hw frame (finProdFinEquiv (i,j))) =
      (frame i).val := by
  simpa only [encodeTuple,Equiv.symm_apply_apply] using
    decode_encodeCounter N w c hN hw (frame i)

theorem stream_counter_decode (N w c Q remaining offset : ℕ)
    (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hQ : Q ≤ N^c)
    (h : offset+remaining ≤ Q) :
    let words := encodeTuple N w c 2 hN hw (streamCounters N c Q remaining offset hQ h)
    decodeWords (fun j => words (finProdFinEquiv ((0 : Fin 2),j))) = remaining ∧
      decodeWords (fun j => words (finProdFinEquiv ((1 : Fin 2),j))) = offset := by
  try dsimp only
  constructor
  · simpa only [streamCounters,Fin.val_zero,↓reduceIte] using
      decode_tuple_field N w c 2 hN hw (streamCounters N c Q remaining offset hQ h) 0
  · simpa only [streamCounters,Fin.val_one,Nat.one_ne_zero,↓reduceIte] using
      decode_tuple_field N w c 2 hN hw (streamCounters N c Q remaining offset hQ h) 1

/-- Four explicit public quantities per stream (base, end, cursor, buffered
length) are charged in addition to payload buffers. This schema is shared by
read and write phases; each entry carries its own polynomial-bound proof. -/
abbrev BucketMetadata (K N c : ℕ) := Fin (4*K) → Fin (N^c+1)

def encodeBucketMetadata (K N w c : ℕ) (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (metadata : BucketMetadata K N c) : Words ((4*K)*(c+1)) w :=
  encodeTuple N w c (4*K) hN hw metadata

theorem bucket_payload_and_metadata (K c B : ℕ) (hB : 0 < B) :
    K*B + (4*K)*(c+1) ≤ (1+4*(c+1))*(K*B) := by
  have h := bucket_metadata_absorbed K 4 c B hB
  nlinarith

/-- A successful physical pop has exactly one read per frame block. -/
theorem pop_transfers {frameWords B w : ℕ} (hB : 0 < B) (stack : Stack B w)
    (frame : Frame frameWords w) (result : StackExecution B w)
    (hdone : pop hB stack = some (frame,result)) :
    result.trace.length = blocksPerFrame frameWords B := by
  by_cases ht : stack.top=0
  · simp [pop,ht] at hdone
  · simp only [pop,if_neg ht,Option.some.injEq,Prod.mk.injEq] at hdone
    rw [← hdone.2]
    simpa only [List.length_nil,Nat.zero_add] using
      popBlocks_transfers hB stack.disk ((stack.top-1)*blocksPerFrame frameWords B)
        (blocksPerFrame frameWords B) (fun _ : Fin frameWords => (0 : Word w)) []

theorem pop_transfer_bound {frameWords B w : ℕ} (hB : 0 < B) (stack : Stack B w)
    (frame : Frame frameWords w) (result : StackExecution B w)
    (hdone : pop hB stack = some (frame,result)) :
    result.trace.length ≤ 1+frameWords/B := by
  rw [pop_transfers hB stack frame result hdone]
  exact blocksPerFrame_bound frameWords B hB

/-- The depth and current field width are bounded by current volume once
that volume contains at least one complete positive-width field. -/
theorem recursion_parameters_le_volume (q m base depth volume : ℕ)
    (hq : 2 ≤ q) (hm : 2 ≤ m) (hbase : 0 < base)
    (hvolume : q^(base*m^depth) ≤ volume) :
    depth ≤ volume ∧ base*m^depth ≤ volume := by
  have hd : depth < m^depth := Nat.lt_pow_self (by omega)
  have hmwidth : m^depth ≤ base*m^depth := Nat.le_mul_of_pos_left _ hbase
  have hw : base*m^depth < q^(base*m^depth) := Nat.lt_pow_self (by omega)
  exact ⟨(hd.le.trans hmwidth).trans (hw.le.trans hvolume),hw.le.trans hvolume⟩

/-- Every dimension of a nonempty five-field file is at most its volume. -/
theorem address_dimensions_le_volume (P Q G S : ℕ)
    (hP : 0 < P) (hQ : 0 < Q) (hG : 0 < G) (hS : 0 < S) :
    P ≤ P*(Q*(G*(Q*S))) ∧ Q ≤ P*(Q*(G*(Q*S))) ∧
      G ≤ P*(Q*(G*(Q*S))) ∧ S ≤ P*(Q*(G*(Q*S))) := by
  have hqs : 0 < Q*S := Nat.mul_pos hQ hS
  have hgqs : 0 < G*(Q*S) := Nat.mul_pos hG hqs
  have hqgqs : 0 < Q*(G*(Q*S)) := Nat.mul_pos hQ hgqs
  have houter : Q*(G*(Q*S)) ≤ P*(Q*(G*(Q*S))) := Nat.le_mul_of_pos_left _ hP
  have hmiddle : G*(Q*S) ≤ Q*(G*(Q*S)) := Nat.le_mul_of_pos_left _ hQ
  have hinner : Q*S ≤ G*(Q*S) := Nat.le_mul_of_pos_left _ hG
  exact ⟨Nat.le_mul_of_pos_right _ hqgqs,
    (Nat.le_mul_of_pos_right _ hgqs).trans houter,
    (Nat.le_mul_of_pos_right _ hqs).trans (hmiddle.trans houter),
    (Nat.le_mul_of_pos_left _ hQ).trans (hinner.trans (hmiddle.trans houter))⟩

section ActualProgramCounter
open MatrixFactorization SpecializedTriangular
variable {m : ℕ} {Family : Type*} [Fintype Family]
variable {A : Family → Matrix (Fin m) (Fin m) ℚ}
variable (F : SpecializedFamily A) (f : ℕ)

/-- Instantiation at the actual specialized, globally lifted triangular
program. Its finite control bound is a theorem about that concrete program. -/
noncomputable def triangularProgramCounterWords (k : Family)
    (hdiag : ∀ i, A k i i ≠ 0) (P S : ℕ) (hS : 0 < S) (w : ℕ) (hw : 1 ≤ w)
    (pc : Fin ((GlobalTriangular.program F f k hdiag P S hS).length+1)) :
    Words (Nat.clog 2 (12*m+1)) w :=
  programCounterWords m w hw (GlobalTriangular.program F f k hdiag P S hS)
    (TriangularProgramBounds.global_length F f k hdiag P S hS) pc

theorem triangularProgramCounter_decode (k : Family)
    (hdiag : ∀ i, A k i i ≠ 0) (P S : ℕ) (hS : 0 < S) (w : ℕ) (hw : 1 ≤ w)
    (pc : Fin ((GlobalTriangular.program F f k hdiag P S hS).length+1)) :
    decodeWords (triangularProgramCounterWords F f k hdiag P S hS w hw pc) = pc.val :=
  decode_programCounterWords _ _ _ _ _ _

end ActualProgramCounter

end CSL.WordControl
end WordControl

section BitWordPacking
/-! A physical block contains B global words, hence B*w bits. This module
uses a position-preserving word/bit codec and simulates a bounded bank
machine through that codec. It does not charge a second disk permutation
for merely viewing the very same block as bits. Payload banks and control
word budgets must still be combined by the caller. -/
set_option autoImplicit false
namespace CSL.BitWordPacking
open CSL.Circuit CSL.WordControl

/-- The digits of one fixed-width global word. -/
def wordBits (w : ℕ) : Word w ≃ (Fin w → Bit) :=
  finFunctionFinEquiv.symm.trans
    (Equiv.piCongrRight (fun _ : Fin w => (ZMod.finEquiv 2).toEquiv))

/-- Consecutive bits of consecutive words in the same physical block. -/
def blockBits (B w : ℕ) : (Fin B → Word w) ≃ (Fin (B*w) → Bit) where
  toFun words i := wordBits w (words (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2
  invFun bits j := (wordBits w).symm (fun i => bits (finProdFinEquiv (j,i)))
  left_inv words := by
    funext j
    simp only [Equiv.symm_apply_apply]
  right_inv bits := by
    funext i
    simp only [Equiv.apply_symm_apply,Prod.mk.eta]

@[simp] theorem blockBits_at (B w : ℕ) (words : Fin B → Word w)
    (j : Fin B) (i : Fin w) :
    blockBits B w words (finProdFinEquiv (j,i)) = wordBits w (words j) i := by
  simp only [blockBits,Equiv.coe_fn_mk,Equiv.symm_apply_apply]

/-- This is the literal within-block position, rather than an arbitrary
finite-type equivalence whose order could conceal a data movement. -/
theorem bit_address (B w : ℕ) (j : Fin B) (i : Fin w) :
    (finProdFinEquiv (j,i)).val = j.val*w+i.val := by
  change i.val+w*j.val=j.val*w+i.val
  ac_rfl

abbrev RAM (Bank : Type*) (R : ℕ) := Fin R → Bank

structure State (Bank : Type*) (R : ℕ) where
  ram : RAM Bank R
  disk : ℕ → Bank

inductive Operation (Bank : Type*) (R : ℕ) where
  | read (address : ℕ) (bank : Fin R)
  | write (address : ℕ) (bank : Fin R)
  | cpu (f : RAM Bank R → RAM Bank R)

variable {X Y : Type*} {R : ℕ}

def transferCost : Operation X R → ℕ
  | .read _ _ => 1
  | .write _ _ => 1
  | .cpu _ => 0

def step (op : Operation X R) (s : State X R) : State X R :=
  match op with
  | .read address bank => ⟨Function.update s.ram bank (s.disk address),s.disk⟩
  | .write address bank => ⟨s.ram,Function.update s.disk address (s.ram bank)⟩
  | .cpu f => ⟨f s.ram,s.disk⟩

def mapRAM (e : X ≃ Y) (ram : RAM X R) : RAM Y R := e ∘ ram

def mapState (e : X ≃ Y) (s : State X R) : State Y R :=
  ⟨mapRAM e s.ram,e ∘ s.disk⟩

@[simp] theorem mapRAM_inverse (e : X ≃ Y) (ram : RAM X R) :
    mapRAM e.symm (mapRAM e ram) = ram := by
  funext i
  exact e.symm_apply_apply _

@[simp] theorem mapState_inverse (e : X ≃ Y) (s : State X R) :
    mapState e.symm (mapState e s) = s := by
  cases s
  simp only [mapState,mapRAM_inverse]
  congr 1
  funext i
  exact e.symm_apply_apply _

/-- Local computation is conjugated inside the existing resident banks;
read/write operations retain the very same block address and bank. -/
def mapOperation (e : X ≃ Y) : Operation X R → Operation Y R
  | .read a r => .read a r
  | .write a r => .write a r
  | .cpu f => .cpu (fun ram => mapRAM e (f (mapRAM e.symm ram)))

@[simp] theorem mapOperation_cost (e : X ≃ Y) (op : Operation X R) :
    transferCost (mapOperation e op) = transferCost op := by
  cases op <;> rfl

private theorem map_update {I : Type*} [DecidableEq I]
    (e : X ≃ Y) (f : I → X) (i : I) (x : X) :
    e ∘ Function.update f i x = Function.update (e ∘ f) i (e x) := by
  funext j
  by_cases h : j=i
  · subst j; simp
  · simp [Function.update_of_ne h]

@[simp] theorem map_step (e : X ≃ Y) (op : Operation X R) (s : State X R) :
    step (mapOperation e op) (mapState e s) = mapState e (step op s) := by
  cases op with
  | read a r =>
    simp only [mapOperation,step,mapState,mapRAM,map_update,Function.comp_apply]
  | write a r =>
    simp only [mapOperation,step,mapState,mapRAM,map_update,Function.comp_apply]
  | cpu f => simp only [mapOperation,step,mapState,mapRAM_inverse]

abbrev Policy (Bank : Type*) (R : ℕ) := RAM Bank R → Option (Operation Bank R)

def run (policy : Policy X R) : ℕ → State X R → State X R × ℕ
  | 0,s => (s,0)
  | k+1,s => match policy s.ram with
    | none => (s,0)
    | some op =>
      let rest := run policy k (step op s)
      (rest.1,transferCost op+rest.2)

def mapPolicy (e : X ≃ Y) (policy : Policy X R) : Policy Y R :=
  fun ram => (policy (mapRAM e.symm ram)).map (mapOperation e)

@[simp] theorem mapPolicy_at (e : X ≃ Y) (policy : Policy X R) (ram : RAM X R) :
    mapPolicy e policy (mapRAM e ram) = (policy ram).map (mapOperation e) := by
  simp only [mapPolicy,mapRAM_inverse]

/-- Every finite RAM-controlled execution is preserved exactly, including
its actual disk contents and its number of physical block transfers. -/
theorem run_map (e : X ≃ Y) (policy : Policy X R) (fuel : ℕ) (s : State X R) :
    run (mapPolicy e policy) fuel (mapState e s) =
      (mapState e (run policy fuel s).1,(run policy fuel s).2) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ k ih =>
    have hp' := mapPolicy_at e policy s.ram
    change mapPolicy e policy (mapState e s).ram = _ at hp'
    cases hp : policy s.ram with
    | none =>
      simp only [run,hp',hp]
      rfl
    | some op =>
      simp only [run,hp',hp]
      try dsimp only [Option.map]
      rw [map_step,ih,mapOperation_cost]

/-- Specialization from bit banks to physical word banks. No bit block
stands for B bits: its size is exactly B*w, the bits of B words. -/
theorem bit_program_word_simulation (B w R : ℕ)
    (policy : Policy (Fin (B*w) → Bit) R) (fuel : ℕ)
    (s : State (Fin (B*w) → Bit) R) :
    run (mapPolicy (blockBits B w).symm policy) fuel
      (mapState (blockBits B w).symm s) =
    (mapState (blockBits B w).symm (run policy fuel s).1,
      (run policy fuel s).2) :=
  run_map (blockBits B w).symm policy fuel s

theorem resident_word_budget (R B w M : ℕ) (h : R*B ≤ M) :
    Fintype.card (Fin R × Fin B) ≤ M ∧ R*(B*w) ≤ M*w := by
  constructor
  · simpa only [Fintype.card_prod,Fintype.card_fin] using h
  · calc R*(B*w) = (R*B)*w := by ac_rfl
         _ ≤ M*w := Nat.mul_le_mul_right w h

end CSL.BitWordPacking
end BitWordPacking

section WordConvention
/-! Constant-word address encodings for an arbitrary fixed lower constant
in the word-size convention. The word width is never enlarged. This module
does not assert that these words fit in the extreme two-word memory case. -/
set_option autoImplicit false
namespace CSL.WordConvention
open WordControl

/-- `c` is fixed by the word-size convention, not by the input values.
The case `c = 1` is the stronger convention used in older interfaces. -/
def Covers (N w c : ℕ) : Prop := Nat.clog 2 N ≤ c*w

theorem covers_capacity (N w c : ℕ) (h : Covers N w c) :
    N ≤ (2^w)^c := by
  have hp : N ≤ 2^(c*w) := (Nat.le_pow_iff_clog_le (by omega)).2 h
  simpa only [←pow_mul,Nat.mul_comm w c] using hp

theorem positive_words (N w c : ℕ) (hN : 2 ≤ N) (h : Covers N w c) :
    0<w ∧ 0<c := by
  have hc := covers_capacity N w c h
  constructor
  · by_contra hn
    have he : w=0 := by omega
    simp [he] at hc
    omega
  · by_contra hn
    have he : c=0 := by omega
    simp [he] at hc
    omega

/-- Endpoints are included. The additional factor `c` is charged in the
resident state instead of being hidden in an enlarged global word. -/
theorem polynomial_capacity (N w c exponent : ℕ) (hN : 2 ≤ N)
    (h : Covers N w c) :
    N^exponent+1 ≤ (2^w)^(c*(exponent+1)) := by
  have hp : 0<N^exponent := pow_pos (by omega) _
  have hstep : N^exponent+1 ≤ N^(exponent+1) := by
    rw [pow_succ]
    nlinarith
  have hc := Nat.pow_le_pow_left (covers_capacity N w c h) (exponent+1)
  rw [←pow_mul] at hc
  exact hstep.trans hc

def encode (N w c exponent : ℕ) (hN : 2 ≤ N) (h : Covers N w c)
    (x : Fin (N^exponent+1)) : Words (c*(exponent+1)) w :=
  finFunctionFinEquiv.symm (x.castLE (polynomial_capacity N w c exponent hN h))

@[simp] theorem decode_encode (N w c exponent : ℕ) (hN : 2 ≤ N)
    (h : Covers N w c) (x : Fin (N^exponent+1)) :
    decodeWords (encode N w c exponent hN h x)=x.val := by
  simp only [decodeWords,encode,Equiv.apply_symm_apply,Fin.coe_castLE]

theorem encode_injective (N w c exponent : ℕ) (hN : 2 ≤ N)
    (h : Covers N w c) : Function.Injective (encode N w c exponent hN h) := by
  intro x y he
  apply Fin.ext
  simpa only [decode_encode] using congrArg decodeWords he

def encodeTuple (N w c exponent fields : ℕ) (hN : 2 ≤ N) (h : Covers N w c)
    (values : Fin fields → Fin (N^exponent+1)) :
    Words (fields*(c*(exponent+1))) w :=
  fun i => encode N w c exponent hN h (values (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2

theorem encodeTuple_injective (N w c exponent fields : ℕ)
    (hN : 2 ≤ N) (h : Covers N w c) :
    Function.Injective (encodeTuple N w c exponent fields hN h) := by
  intro x y he
  funext i
  apply encode_injective N w c exponent hN h
  funext j
  have hv := congrFun he (finProdFinEquiv (i,j))
  simpa only [encodeTuple,Equiv.symm_apply_apply] using hv

/-- A finite address port of the proved polynomial range is directly
encoded in the same global word type as payload data. -/
theorem address_recovery (N w c exponent : ℕ) (hN : 2 ≤ N)
    (h : Covers N w c) (address : ℕ) (ha : address ≤ N^exponent) :
    decodeWords (encode N w c exponent hN h ⟨address,by omega⟩)=address :=
  decode_encode N w c exponent hN h _

theorem one_word_convention (N w : ℕ) (h : Nat.clog 2 N ≤ w) : Covers N w 1 := by
  simpa only [Covers,one_mul] using h

end CSL.WordConvention
end WordConvention


