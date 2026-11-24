-- Prove2me | Definitions.Def_CSL_Shared_Programs_TagErasure
-- name    : CSL_Shared_Programs_TagErasure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:56:05.286635+00:00
-- url     : https://prove2.me/theorems/e02bc670-e245-4bcd-8706-824e53399cbe
-- title:
--   Coded sorting library: Shared / Programs / TagErasure
-- statement:
--   Module `CodedSorting.Shared.Programs.TagErasure` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Payload-only buffered streams with public address counters
--
--   Address tags are proof annotations, not stored records. The actual dispatcher
--   computes a stream key from its public input counter and appends only the
--   payload; the actual reader computes the next stream from its public output
--   counter. Mapping away tags commutes with every writer flush and reader refill,
--   preserving the exact transfer count and payload-buffer occupancy.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.TagErasure

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_AffineStreams

/-!
# Payload-only buffered streams with public address counters

Address tags are proof annotations, not stored records. The actual dispatcher
computes a stream key from its public input counter and appends only the
payload; the actual reader computes the next stream from its public output
counter. Mapping away tags commutes with every writer flush and reader refill,
preserving the exact transfer count and payload-buffer occupancy.
-/

set_option autoImplicit false

namespace CSL.TagErasure

open BucketMachine BucketReader AffineStreams SequentialArithmetic

variable {α β Value : Type*} {Q K : ℕ}

def mapWriter (f : α → β) (s : Writer α) : Writer β :=
  ⟨s.blocks.map (List.map f), s.pending.map f⟩

def mapReader (f : α → β) (s : Reader α) : Reader β :=
  ⟨s.disk.map (List.map f), s.pending.map f, s.reads⟩

@[simp] theorem mapWriter_empty (f : α → β) : mapWriter f Writer.empty = Writer.empty := rfl

@[simp] theorem mapWriter_push (f : α → β) (B : ℕ) (s : Writer α) (a : α) :
    mapWriter f (s.push B a) = (mapWriter f s).push B (f a) := by
  by_cases h : s.pending.length + 1 = B <;>
    simp [Writer.push, mapWriter, List.length_append, h]

@[simp] theorem mapWriter_finish (f : α → β) (s : Writer α) :
    (mapWriter f s).finish = s.finish.map (List.map f) := by
  cases s with
  | mk blocks pending => cases pending <;> simp [mapWriter, Writer.finish]

@[simp] theorem mapReader_fromDisk (f : α → β) (blocks : List (List α)) :
    mapReader f (Reader.fromDisk blocks) = Reader.fromDisk (blocks.map (List.map f)) := rfl

@[simp] theorem mapReader_pop (f : α → β) (s : Reader α) :
    (mapReader f s).pop = s.pop.map (fun result => (f result.1, mapReader f result.2)) := by
  rcases s with ⟨disk,pending,reads⟩
  cases pending with
  | cons a rest => rfl
  | nil =>
    cases disk with
    | nil => rfl
    | cons block disk => cases block <;> rfl

@[simp] theorem mapReader_reads (f : α → β) (s : Reader α) :
    (mapReader f s).reads = s.reads := rfl

@[simp] theorem mapReader_pending_length (f : α → β) (s : Reader α) :
    (mapReader f s).pending.length = s.pending.length := by simp [mapReader, mapWriter]

@[simp] theorem mapWriter_pending_length (f : α → β) (s : Writer α) :
    (mapWriter f s).pending.length = s.pending.length := by simp [mapReader, mapWriter]

theorem readSchedule_map (f : α → β) (schedule : List (Fin K))
    (state : Fin K → Reader α) :
    readSchedule schedule (fun k => mapReader f (state k)) =
      (readSchedule schedule state).map
        (fun result => (result.1.map f, fun k => mapReader f (result.2 k))) := by
  induction schedule generalizing state with
  | nil => rfl
  | cons k rest ih =>
    rw [readSchedule, mapReader_pop]
    cases hp : (state k).pop with
    | none => simp [hp, readSchedule]
    | some result =>
      rcases result with ⟨a,next⟩
      try dsimp only [Option.map]
      have hnext : (fun j => if j = k then mapReader f next else mapReader f (state j)) =
          (fun j => mapReader f (if j = k then next else state j)) := by
        funext j
        split_ifs <;> rfl
      rw [hnext, ih]
      simp only [readSchedule, hp]
      cases readSchedule rest (fun j => if j = k then next else state j) <;> rfl

@[simp] theorem readCount_map (f : α → β) (state : Fin K → Reader α) :
    readCount (fun k => mapReader f (state k)) = readCount state := rfl

@[simp] theorem occupiedReaders_map (f : α → β) (state : Fin K → Reader α) :
    occupiedReaders (fun k => mapReader f (state k)) = occupiedReaders state := by
  simp only [occupiedReaders, mapReader_pending_length]

/-- A public list of indices used only to express the loop's semantic trace.
The actual loops below keep `offset` and `remaining`, not this list. -/
def indices (remaining offset : ℕ) (bound : offset + remaining ≤ Q) : List (Fin Q) :=
  List.ofFn (fun i : Fin remaining => ⟨offset + i.val, by omega⟩)

@[simp] theorem indices_zero (offset : ℕ) (bound : offset + 0 ≤ Q) :
    indices 0 offset bound = [] := rfl

theorem indices_succ (n offset : ℕ) (bound : offset + (n+1) ≤ Q) :
    indices (n+1) offset bound =
      ⟨offset, by omega⟩ :: indices n (offset+1) (by omega) := by
  simp only [indices, List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

@[simp] theorem indices_full : indices Q 0 (by omega) = List.finRange Q := by
  simp only [indices, Nat.zero_add, Fin.eta]
  exact List.ofFn_id Q

/-- Dispatch one payload using a public stream number. No address appears in
any on-disk block or in-memory payload buffer. -/
def pushValue (B : ℕ) (stream : Fin K) (value : Value)
    (state : Fin K → Writer Value) : Fin K → Writer Value :=
  fun k => if stream = k then (state k).push B value else state k

/-- Consume input addresses in increasing order, with two bounded counters.
`F` denotes the already-existing input array, not a newly allocated table. -/
def writeIndexed (key : Fin Q → Fin K) (F : Fin Q → Value) (B : ℕ) :
    (remaining offset : ℕ) → offset + remaining ≤ Q →
      (Fin K → Writer Value) → (Fin K → Writer Value)
  | 0, _, _, state => state
  | n+1, offset, bound, state =>
      let x : Fin Q := ⟨offset, by omega⟩
      writeIndexed key F B n (offset+1) (by omega)
        (pushValue B (key x) (F x) state)

theorem writeIndexed_erasure (key : Fin Q → Fin K) (F : Fin Q → Value) (B : ℕ)
    (remaining offset : ℕ) (bound : offset + remaining ≤ Q)
    (state : Fin K → Writer (Fin Q × Value)) :
    writeIndexed key F B remaining offset bound (fun k => mapWriter Prod.snd (state k)) =
      (fun k => mapWriter Prod.snd
        (runBuckets (fun r : Fin Q × Value => key r.1) B
          ((indices remaining offset bound).map (fun x => (x,F x))) state k)) := by
  induction remaining generalizing offset state with
  | zero => rfl
  | succ n ih =>
    rw [writeIndexed, indices_succ]
    simp only [List.map_cons, runBuckets, List.foldl_cons]
    have hnext : pushValue B (key ⟨offset, by omega⟩) (F ⟨offset, by omega⟩)
        (fun k => mapWriter Prod.snd (state k)) =
        (fun k => mapWriter Prod.snd
          (bucketStep (fun r : Fin Q × Value => key r.1) B state
            (⟨offset, by omega⟩, F ⟨offset, by omega⟩) k)) := by
      funext k
      simp only [pushValue, bucketStep]
      split_ifs <;> simp only [mapWriter_push]
    rw [hnext]
    exact ih (offset+1) (by omega) _

def valueWriters (key : Fin Q → Fin K) (F : Fin Q → Value) (B : ℕ) :
    Fin K → Writer Value :=
  writeIndexed key F B Q 0 (by omega) (fun _ => Writer.empty)

theorem valueWriters_erasure (key : Fin Q → Fin K) (F : Fin Q → Value) (B : ℕ) :
    valueWriters key F B = fun k => mapWriter Prod.snd
      (bufferedBuckets (fun r : Fin Q × Value => key r.1) B (inputRecords F) k) := by
  simpa only [valueWriters, mapWriter_empty, indices_full, bufferedBuckets, inputRecords] using
    writeIndexed_erasure key F B Q 0 (by omega) (fun _ => Writer.empty)

/-- Head-only reading driven by the public output address. Its key is computed
from `e.symm y`; no stored tag is inspected or retained. -/
def readIndexed (schedule : Fin Q → Fin K) :
    (remaining offset : ℕ) → offset + remaining ≤ Q →
      (Fin K → Reader Value) → Option (List Value × (Fin K → Reader Value))
  | 0, _, _, state => some ([],state)
  | n+1, offset, bound, state =>
      match (state (schedule ⟨offset, by omega⟩)).pop with
      | none => none
      | some (value,next) =>
          match readIndexed schedule n (offset+1) (by omega)
            (fun k => if k = schedule ⟨offset, by omega⟩ then next else state k) with
          | none => none
          | some (out,final) => some (value::out,final)

theorem readIndexed_eq_schedule (schedule : Fin Q → Fin K)
    (remaining offset : ℕ) (bound : offset + remaining ≤ Q)
    (state : Fin K → Reader Value) :
    readIndexed schedule remaining offset bound state =
      readSchedule ((indices remaining offset bound).map schedule) state := by
  induction remaining generalizing offset state with
  | zero => rfl
  | succ n ih =>
    rw [readIndexed, indices_succ]
    simp only [List.map_cons, readSchedule]
    cases (state (schedule ⟨offset, by omega⟩)).pop with
    | none => rfl
    | some result =>
      rcases result with ⟨value,next⟩
      try dsimp only
      rw [ih]
      rfl

def valueReaders (key : Fin Q → Fin K) (F : Fin Q → Value) (B : ℕ) :
    Fin K → Reader Value :=
  fun k => Reader.fromDisk (valueWriters key F B k).finish

theorem valueReaders_erasure (key : Fin Q → Fin K) (F : Fin Q → Value) (B : ℕ) :
    valueReaders key F B = fun k => mapReader Prod.snd
      (initialReaders (fun r : Fin Q × Value => key r.1) B (inputRecords F) k) := by
  funext k
  simp only [valueReaders, valueWriters_erasure, mapWriter_finish,
    initialReaders, mapReader_fromDisk]

def inputValues (F : Fin Q → Value) := (List.finRange Q).map F

def outputValues (e : Equiv.Perm (Fin Q)) (F : Fin Q → Value) :=
  (List.finRange Q).map (fun y => F (e.symm y))

def valueFlushCount (key : Fin Q → Fin K) (F : Fin Q → Value) (B : ℕ) : ℕ :=
  ((List.finRange K).map (fun k => (valueWriters key F B k).finish.length)).sum

theorem valueFlushCount_erasure (key : Fin Q → Fin K) (F : Fin Q → Value) (B : ℕ) :
    valueFlushCount key F B =
      flushCount (fun r : Fin Q × Value => key r.1) B (inputRecords F) := by
  simp only [valueFlushCount, valueWriters_erasure, mapWriter_finish, List.length_map,
    flushCount]

/-- Every term counts transfers of blocks containing only `Value`, including
input/output scans and all bucket flushes/refills. -/
def valueTransfers (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (F : Fin Q → Value) (B : ℕ) (hB : 0 < B) (final : Fin K → Reader Value) : ℕ :=
  (pack B hB (inputValues F)).length + valueFlushCount key F B +
    readCount final + (pack B hB (outputValues e F)).length

theorem valueTransfers_erasure (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (F : Fin Q → Value) (B : ℕ) (hB : 0 < B)
    (final : Fin K → Reader (Fin Q × Value)) :
    valueTransfers e key F B hB (fun k => mapReader Prod.snd (final k)) =
      completeTransfers (fun r : Fin Q × Value => key r.1) B hB
        (inputRecords F) (targetRecords e F) final := by
  simp only [valueTransfers, completeTransfers, valueFlushCount_erasure, readCount_map,
    pack_count, inputValues, outputValues, inputRecords, targetRecords, targetSources,
    List.length_map]

/-- The transfer bound counts stored data values. The loops compute stream addresses from their counters. 
-/
theorem increasing_value_reconstruction (e : Equiv.Perm (Fin Q))
    (key : Fin Q → Fin K)
    (hinc : ∀ x y, x < y → key x = key y → e x < e y)
    (F : Fin Q → Value) (B : ℕ) (hB : 0 < B) :
    ∃ final,
      readIndexed (fun y => key (e.symm y)) Q 0 (by omega) (valueReaders key F B) =
        some (outputValues e F,final) ∧
      valueTransfers e key F B hB final ≤ 4 * (Q / B) + 2 * K + 2 ∧
      occupiedReaders final ≤ K * B := by
  obtain ⟨final,hread,hcost,hmem⟩ := payload_reconstruction e key hinc F B hB
  refine ⟨fun k => mapReader Prod.snd (final k), ?_, ?_, ?_⟩
  · rw [readIndexed_eq_schedule, indices_full, valueReaders_erasure, readSchedule_map]
    have hschedule : (List.finRange Q).map (fun y => key (e.symm y)) =
        (targetRecords e F).map (fun r => key r.1) := by
      simp only [targetRecords, targetSources, List.map_map, Function.comp_def]
    rw [hschedule,hread]
    try dsimp only [Option.map]
    rw [targetRecords_payloads]
    rfl
  · rw [valueTransfers_erasure]
    exact hcost
  · simpa only [occupiedReaders_map] using hmem

def writerOccupancy (state : Fin K → Writer Value) : ℕ :=
  ((List.finRange K).map (fun k => (state k).pending.length)).sum

/-- All intermediate input prefixes use at most K*B payload units of bucket
RAM; address tags have not been hidden in a supposedly single-unit record. -/
theorem writeIndexed_memory (key : Fin Q → Fin K) (F : Fin Q → Value)
    (B : ℕ) (hB : 0 < B) (remaining offset : ℕ) (bound : offset + remaining ≤ Q) :
    writerOccupancy
      (writeIndexed key F B remaining offset bound (fun _ => Writer.empty)) ≤ K * B := by
  have h := writeIndexed_erasure key F B remaining offset bound (fun _ => Writer.empty)
  simp only [mapWriter_empty] at h
  rw [h]
  unfold writerOccupancy
  simp only [mapWriter_pending_length]
  exact bucket_memory_bound (fun r : Fin Q × Value => key r.1) B hB
    ((indices remaining offset bound).map (fun x => (x,F x)))

/-- The public loop's only position counters never exceed Q. A computed
stream number is a Fin K, hence also fits one bounded control integer. -/
theorem public_counters_bounded (remaining offset : ℕ) (bound : offset + remaining ≤ Q)
    (stream : Fin K) : remaining ≤ Q ∧ offset ≤ Q ∧ stream.val < K := by
  exact ⟨by omega, by omega, stream.isLt⟩

/-- Fixed modular multiplication implemented without storing a tag per bit. -/
theorem multiplication_value_reconstruction {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hcoprime : a.Coprime Q) (F : Fin Q → Value) (B : ℕ) (hB : 0 < B) :
    let e := multiplicationEquiv hQ hcoprime
    let key := multiplicationRun ha hQ
    ∃ final,
      readIndexed (fun y => key (e.symm y)) Q 0 (by omega) (valueReaders key F B) =
        some (outputValues e F,final) ∧
      valueTransfers e key F B hB final ≤ 4 * (Q / B) + 2 * a + 2 ∧
      occupiedReaders final ≤ a * B := by
  try dsimp only
  apply increasing_value_reconstruction _ _ _ F B hB
  intro x y hxy hr
  exact multiplication_increasing_in_run ha hQ x y hxy hr

/-- The inverse uses the same number of payload buffers. -/
theorem inverse_multiplication_value_reconstruction {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hcoprime : a.Coprime Q) (F : Fin Q → Value) (B : ℕ) (hB : 0 < B) :
    let e := multiplicationEquiv hQ hcoprime
    let key := fun x => multiplicationRun ha hQ (e.symm x)
    ∃ final,
      readIndexed (fun y => key (e y)) Q 0 (by omega) (valueReaders key F B) =
        some (outputValues e.symm F,final) ∧
      valueTransfers e.symm key F B hB final ≤ 4 * (Q / B) + 2 * a + 2 ∧
      occupiedReaders final ≤ a * B := by
  try dsimp only
  exact increasing_value_reconstruction (multiplicationEquiv hQ hcoprime).symm
    (fun x => multiplicationRun ha hQ ((multiplicationEquiv hQ hcoprime).symm x))
    (inverse_increasing_streams _ _
      (fun x y hxy hr => multiplication_increasing_in_run ha hQ x y hxy hr)) F B hB

/-- Fixed modular addition needs only two payload buffers. -/
theorem addition_value_reconstruction (c : Fin Q) (F : Fin Q → Value)
    (B : ℕ) (hB : 0 < B) :
    let e := additionEquiv c
    let key := additionRun c
    ∃ final,
      readIndexed (fun y => key (e.symm y)) Q 0 (by omega) (valueReaders key F B) =
        some (outputValues e F,final) ∧
      valueTransfers e key F B hB final ≤ 4 * (Q / B) + 6 ∧
      occupiedReaders final ≤ 2 * B := by
  try dsimp only
  apply increasing_value_reconstruction _ _ _ F B hB
  exact fun x y hxy hr => addition_increasing_in_run c x y hxy hr

theorem mapReader_valid (f : α → β) (B : ℕ) (state : Reader α)
    (h : state.Valid B) : (mapReader f state).Valid B := by
  constructor
  · intro block hb
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hb
    simpa only [List.length_map] using h.1 old hold
  · simpa only [mapReader_pending_length] using h.2

theorem valueReaders_valid (key : Fin Q → Fin K) (F : Fin Q → Value)
    (B : ℕ) (hB : 0 < B) (k : Fin K) : (valueReaders key F B k).Valid B := by
  rw [valueReaders_erasure]
  apply mapReader_valid
  exact initialReaders_valid _ B hB _ k

/-- Every prefix of the public read loop preserves all block-buffer bounds. -/
theorem readIndexed_valid (schedule : Fin Q → Fin K) (B : ℕ)
    (remaining offset : ℕ) (bound : offset + remaining ≤ Q)
    (state : Fin K → Reader Value) (hv : ∀ k, (state k).Valid B)
    (out : List Value) (final : Fin K → Reader Value)
    (hdone : readIndexed schedule remaining offset bound state = some (out,final)) :
    ∀ k, (final k).Valid B := by
  induction remaining generalizing offset state out final with
  | zero =>
    simp only [readIndexed,Option.some.injEq,Prod.mk.injEq] at hdone
    obtain ⟨rfl,rfl⟩ := hdone
    exact hv
  | succ n ih =>
    cases hp : (state (schedule ⟨offset,by omega⟩)).pop with
    | none => simp [readIndexed,hp] at hdone
    | some result =>
      rcases result with ⟨a,next⟩
      let updated := fun k => if k = schedule ⟨offset,by omega⟩ then next else state k
      have hn : ∀ k, (updated k).Valid B := by
        intro k
        by_cases hk : k = schedule ⟨offset,by omega⟩
        · subst k
          simpa only [updated,↓reduceIte] using Reader.pop_valid B _ _ a (hv _) hp
        · simpa only [updated,if_neg hk] using hv k
      cases hr : readIndexed schedule n (offset+1) (by omega) updated with
      | none => simp [readIndexed,hp,show (fun k =>
          if k = schedule ⟨offset,by omega⟩ then next else state k) = updated from rfl,hr] at hdone
      | some result =>
        rcases result with ⟨out',final'⟩
        have hc : a :: out' = out ∧ final' = final := by
          simpa only [readIndexed,hp,hr,updated,Option.some.injEq,Prod.mk.injEq] using hdone
        rw [← hc.2]
        exact ih (offset+1) (by omega) updated hn out' final' hr

/-- Reader RAM is bounded throughout execution, not only after the streams
have been exhausted. Each stored unit here has type Value alone. -/
theorem readIndexed_memory (key schedule : Fin Q → Fin K) (F : Fin Q → Value)
    (B : ℕ) (hB : 0 < B) (n : ℕ) (hn : n ≤ Q)
    (out : List Value) (final : Fin K → Reader Value)
    (h : readIndexed schedule n 0 (by omega) (valueReaders key F B) = some (out,final)) :
    occupiedReaders final ≤ K * B :=
  reader_memory B final (readIndexed_valid schedule B n 0 (by omega)
    (valueReaders key F B) (valueReaders_valid key F B hB) out final h)

end CSL.TagErasure


