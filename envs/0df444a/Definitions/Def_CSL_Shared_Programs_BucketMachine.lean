-- Prove2me | Definitions.Def_CSL_Shared_Programs_BucketMachine
-- name    : CSL_Shared_Programs_BucketMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:20:44.297011+00:00
-- url     : https://prove2.me/theorems/1f9ed6bf-dedc-4fa3-9813-b337b0769067
-- title:
--   Coded sorting library: Shared / Programs / BucketMachine
-- statement:
--   Module `CodedSorting.Shared.Programs.BucketMachine` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Concrete bucket streams and block transfers
--
--   This module defines the streams and their physical blocks as finite lists.
--   Each element denotes one fixed-size storage unit.  One block transfer moves
--   one list of at most B such units.  Costs are counted from those actual lists
--   of blocks, rather than supplied as a scan-cost hypothesis.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.BucketMachine

import Definitions.Def_CSL_Compat
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CSL_Shared_Indexing_BucketOrder
import Definitions.Def_CSL_Shared_Memory_Address
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Count
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Concrete bucket streams and block transfers

This module defines the streams and their physical blocks as finite lists.
Each element denotes one fixed-size storage unit.  One block transfer moves
one list of at most B such units.  Costs are counted from those actual lists
of blocks, rather than supplied as a scan-cost hypothesis.
-/

namespace CSL.BucketMachine

variable {α : Type*} {K : ℕ}

/-- The output stream for one bucket, in input order. -/
def bucket (key : α → Fin K) (xs : List α) (k : Fin K) : List α :=
  xs.filter (fun a => key a == k)

/-- Concatenate streams in increasing bucket-number order. -/
def collect (key : α → Fin K) (xs : List α) : List α :=
  (List.finRange K).flatMap (bucket key xs)

theorem bucket_sublist (key : α → Fin K) (xs : List α) (k : Fin K) :
    (bucket key xs k).Sublist xs := List.filter_sublist

theorem mem_bucket (key : α → Fin K) (xs : List α) (k : Fin K) (a : α) :
    a ∈ bucket key xs k ↔ a ∈ xs ∧ key a = k := by simp [bucket]

private theorem sum_single_key {β : Type*} [DecidableEq β]
    (keys : List β) (hn : keys.Nodup) (a : β) (c : ℕ) :
    (keys.map (fun k => if a = k then c else 0)).sum = if a ∈ keys then c else 0 := by
  induction keys with
  | nil => simp
  | cons k keys ih =>
    have h := List.nodup_cons.mp hn
    by_cases hak : a = k
    · subst a
      simp [h.1, ih h.2]
    · simp [hak, ih h.2]

private theorem count_bucket [DecidableEq α]
    (key : α → Fin K) (xs : List α) (k : Fin K) (a : α) :
    (bucket key xs k).count a = if key a = k then xs.count a else 0 := by
  by_cases h : key a = k
  · simp [bucket, h]
  · have hn : a ∉ bucket key xs k := by simp [mem_bucket, h]
    simp [h, List.count_eq_zero.mpr hn]

/-- No record is lost, duplicated, or changed; multiplicities are retained. -/
theorem collect_perm (key : α → Fin K) (xs : List α) :
    (collect key xs).Perm xs := by
  classical
  apply List.perm_iff_count.mpr
  intro a
  simp only [collect, List.count_flatMap]
  change ((List.finRange K).map (fun k => (bucket key xs k).count a)).sum = xs.count a
  simp_rw [count_bucket]
  rw [sum_single_key _ (List.nodup_finRange K)]
  simp

theorem collect_length (key : α → Fin K) (xs : List α) :
    (collect key xs).length = xs.length := (collect_perm key xs).length_eq

/-- A concrete sequential block writer.  It flushes a full prefix of B units
and continues on the unread suffix.  The final block may be partial. -/
def pack (B : ℕ) (hB : 0 < B) (xs : List α) : List (List α) :=
  match xs with
  | [] => []
  | a :: rest => (a :: rest).take B :: pack B hB ((a :: rest).drop B)
termination_by xs.length
decreasing_by simp; omega

/-- Reading every emitted block in order recovers the exact stream. -/
theorem flatten_pack (B : ℕ) (hB : 0 < B) (xs : List α) :
    (pack B hB xs).flatten = xs := by
  induction xs using pack.induct B hB with
  | case1 => simp [pack]
  | case2 a rest ih =>
    rw [pack, List.flatten_cons, ih]
    exact List.take_append_drop B (a :: rest)

/-- Every actual transfer contains at most B storage units. -/
theorem block_size_bound (B : ℕ) (hB : 0 < B) (xs : List α) :
    ∀ block ∈ pack B hB xs, block.length ≤ B := by
  induction xs using pack.induct B hB with
  | case1 => simp [pack]
  | case2 a rest ih =>
    intro block hb
    rw [pack] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [List.length_take]
      exact Nat.min_le_left _ _
    · exact ih block hb

/-- Exact occupancy bounds for the emitted blocks, including an empty input. -/
theorem pack_capacity (B : ℕ) (hB : 0 < B) (xs : List α) :
    xs.length ≤ (pack B hB xs).length * B ∧
      (pack B hB xs).length * B < xs.length + B := by
  induction xs using pack.induct B hB with
  | case1 => simp [pack, hB]
  | case2 a rest ih =>
    rw [pack]
    simp only [List.length_cons, Nat.add_mul]
    simp only [List.length_drop, List.length_cons] at ih ⊢
    by_cases hlen : (a :: rest).length ≤ B
    · have hdrop : (a :: rest).drop B = [] := List.drop_eq_nil_iff.mpr hlen
      simp only [hdrop, pack, List.length_nil, Nat.zero_mul, Nat.one_mul,
        Nat.zero_add, List.length_cons]
      simp only [List.length_cons] at hlen
      omega
    · simp only [Nat.one_mul]
      simp only [List.length_cons] at hlen
      omega

/-- Number of flushes is exactly ceil(length/B), proved from the block writer. -/
theorem pack_count (B : ℕ) (hB : 0 < B) (xs : List α) :
    (pack B hB xs).length = (xs.length + B - 1) / B := by
  have h := pack_capacity B hB xs
  symm
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [Nat.add_mul]
    omega

/-- The completed blocks are on disk. Only `pending` occupies the bucket's
in-memory block buffer. -/
structure Writer (α : Type*) where
  blocks : List (List α)
  pending : List α

def Writer.empty : Writer α := ⟨[], []⟩

def Writer.contents (s : Writer α) : List α := s.blocks.flatten ++ s.pending

/-- Consume the next unit. Reaching B units emits exactly one block. -/
def Writer.push (B : ℕ) (s : Writer α) (a : α) : Writer α :=
  let next := s.pending ++ [a]
  if next.length = B then ⟨s.blocks ++ [next], []⟩ else ⟨s.blocks, next⟩

/-- End-of-stream: emit a nonempty partial block exactly once. -/
def Writer.finish (s : Writer α) : List (List α) :=
  if s.pending.isEmpty then s.blocks else s.blocks ++ [s.pending]

def Writer.Valid (B : ℕ) (s : Writer α) : Prop :=
  (∀ block ∈ s.blocks, block.length = B) ∧ s.pending.length < B

theorem Writer.push_contents (B : ℕ) (s : Writer α) (a : α) :
    (s.push B a).contents = s.contents ++ [a] := by
  simp only [Writer.push]
  split <;> simp [Writer.contents, List.flatten_append, List.append_assoc]

theorem Writer.finish_contents (s : Writer α) :
    s.finish.flatten = s.contents := by
  cases s with
  | mk blocks pending => cases pending <;> simp [Writer.finish, Writer.contents]

theorem Writer.empty_valid (B : ℕ) (hB : 0 < B) : (Writer.empty : Writer α).Valid B := by
  simp [Writer.Valid, Writer.empty, hB]

theorem Writer.push_valid (B : ℕ) (s : Writer α) (a : α) (hs : s.Valid B) :
    (s.push B a).Valid B := by
  rcases hs with ⟨hblocks, hshort⟩
  unfold Writer.push
  try dsimp only
  split
  · rename_i hfull
    constructor
    · intro block hb
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hblocks block hb
      · exact hfull
    · simp only [List.length_nil]
      omega
  · rename_i hnotfull
    constructor
    · exact hblocks
    · simp only [List.length_append, List.length_singleton] at hnotfull ⊢
      omega

private theorem full_blocks_length (B : ℕ) (blocks : List (List α))
    (h : ∀ block ∈ blocks, block.length = B) :
    blocks.flatten.length = blocks.length * B := by
  induction blocks with
  | nil => simp
  | cons block rest ih =>
    have hb := h block (by simp)
    have hr : ∀ b ∈ rest, b.length = B := fun b hm => h b (by simp [hm])
    simp [hb, ih hr, Nat.add_mul, Nat.add_comm]

theorem Writer.finish_capacity (B : ℕ) (s : Writer α) (hs : s.Valid B) :
    s.contents.length ≤ s.finish.length * B ∧
      s.finish.length * B < s.contents.length + B := by
  obtain ⟨hblocks, hshort⟩ := hs
  have hlen := full_blocks_length B s.blocks hblocks
  by_cases he : s.pending = []
  · simp [Writer.finish, Writer.contents, he, hlen]
    simp [he] at hshort
    exact hshort
  · have hpos : 0 < s.pending.length := List.length_pos_iff.mpr he
    have hempty : s.pending.isEmpty = false := by simpa using he
    simp only [Writer.finish, hempty, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton,
      Writer.contents, Nat.add_mul, Nat.one_mul, hlen]
    omega

theorem Writer.finish_count (B : ℕ) (s : Writer α) (hs : s.Valid B) :
    s.finish.length = (s.contents.length + B - 1) / B := by
  have h := s.finish_capacity B hs
  symm
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [Nat.add_mul]
    omega

/-- One streaming input step touches only the selected bucket's writer. -/
def bucketStep (key : α → Fin K) (B : ℕ)
    (state : Fin K → Writer α) (a : α) : Fin K → Writer α :=
  fun k => if key a = k then (state k).push B a else state k

/-- A left-to-right scan with K independently buffered output streams. -/
def runBuckets (key : α → Fin K) (B : ℕ) (xs : List α)
    (initial : Fin K → Writer α) : Fin K → Writer α :=
  xs.foldl (bucketStep key B) initial

theorem runBuckets_contents (key : α → Fin K) (B : ℕ) (xs : List α)
    (initial : Fin K → Writer α) (k : Fin K) :
    (runBuckets key B xs initial k).contents =
      (initial k).contents ++ bucket key xs k := by
  induction xs generalizing initial with
  | nil => simp [runBuckets, bucket]
  | cons a rest ih =>
    simp only [runBuckets, List.foldl_cons]
    change (runBuckets key B rest (bucketStep key B initial a) k).contents = _
    rw [ih]
    by_cases hk : key a = k
    · simp [bucketStep, hk, Writer.push_contents, bucket, List.append_assoc]
    · simp [bucketStep, hk, bucket]

theorem runBuckets_valid (key : α → Fin K) (B : ℕ) (xs : List α)
    (initial : Fin K → Writer α) (hi : ∀ k, (initial k).Valid B) :
    ∀ k, (runBuckets key B xs initial k).Valid B := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons a rest ih =>
    apply ih
    intro k
    by_cases hk : key a = k
    · simpa [bucketStep, hk] using Writer.push_valid B (initial k) a (hi k)
    · simpa [bucketStep, hk] using hi k

def bufferedBuckets (key : α → Fin K) (B : ℕ) (xs : List α) : Fin K → Writer α :=
  runBuckets key B xs (fun _ => Writer.empty)

/-- This is an equality of actual lists, and therefore retains all values,
within-bucket order, and duplicate records. -/
theorem buffered_bucket_correct (key : α → Fin K) (B : ℕ) (xs : List α) (k : Fin K) :
    (bufferedBuckets key B xs k).finish.flatten = bucket key xs k := by
  rw [Writer.finish_contents]
  simpa [bufferedBuckets, Writer.empty, Writer.contents] using
    runBuckets_contents key B xs (fun _ => Writer.empty) k

theorem buffered_bucket_valid (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (xs : List α) (k : Fin K) : (bufferedBuckets key B xs k).Valid B :=
  runBuckets_valid key B xs _ (fun _ => Writer.empty_valid B hB) k

theorem buffered_bucket_flushes (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (xs : List α) (k : Fin K) :
    (bufferedBuckets key B xs k).finish.length =
      ((bucket key xs k).length + B - 1) / B := by
  rw [Writer.finish_count B _ (buffered_bucket_valid key B hB xs k)]
  have h := buffered_bucket_correct key B xs k
  rw [Writer.finish_contents] at h
  rw [h]

def bufferedCollect (key : α → Fin K) (B : ℕ) (xs : List α) : List α :=
  (List.finRange K).flatMap (fun k => (bufferedBuckets key B xs k).finish.flatten)

theorem bufferedCollect_correct (key : α → Fin K) (B : ℕ) (xs : List α) :
    bufferedCollect key B xs = collect key xs := by
  simp [bufferedCollect, buffered_bucket_correct, collect]

theorem bufferedCollect_perm (key : α → Fin K) (B : ℕ) (xs : List α) :
    (bufferedCollect key B xs).Perm xs := by
  rw [bufferedCollect_correct]
  exact collect_perm key xs

def flushCount (key : α → Fin K) (B : ℕ) (xs : List α) : ℕ :=
  ((List.finRange K).map (fun k => (bufferedBuckets key B xs k).finish.length)).sum

private theorem sum_transfer_capacity {β : Type*} (keys : List β)
    (cost size : β → ℕ) (B : ℕ)
    (h : ∀ k ∈ keys, cost k * B ≤ size k + B) :
    (keys.map cost).sum * B ≤ (keys.map size).sum + keys.length * B := by
  induction keys with
  | nil => simp
  | cons k rest ih =>
    have hk := h k (by simp)
    have hr := ih (fun k hk => h k (by simp [hk]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem total_bucket_lengths (key : α → Fin K) (xs : List α) :
    ((List.finRange K).map (fun k => (bucket key xs k).length)).sum = xs.length := by
  simpa only [collect, List.length_flatMap, Function.comp_def] using collect_length key xs

/-- Each emitted block is charged once. This upper bound follows from the
concrete writers, with no scan-cost assumption. -/
theorem flush_capacity (key : α → Fin K) (B : ℕ) (hB : 0 < B) (xs : List α) :
    flushCount key B xs * B ≤ xs.length + K * B := by
  have h := sum_transfer_capacity (List.finRange K)
    (fun k => (bufferedBuckets key B xs k).finish.length)
    (fun k => (bucket key xs k).length) B (by
      intro k _
      have hcap := Writer.finish_capacity B _ (buffered_bucket_valid key B hB xs k)
      have hcontent := buffered_bucket_correct key B xs k
      rw [Writer.finish_contents] at hcontent
      rw [hcontent] at hcap
      exact Nat.le_of_lt hcap.2)
  simpa only [flushCount, total_bucket_lengths, List.length_finRange] using h

theorem flush_count_bound (key : α → Fin K) (B : ℕ) (hB : 0 < B) (xs : List α) :
    flushCount key B xs ≤ xs.length / B + K := by
  have h := (Nat.le_div_iff_mul_le hB).2 (flush_capacity key B hB xs)
  simpa only [Nat.add_mul_div_right _ _ hB] using h

private theorem sum_uniform_bound {β : Type*} (keys : List β) (size : β → ℕ) (B : ℕ)
    (h : ∀ k ∈ keys, size k ≤ B) : (keys.map size).sum ≤ keys.length * B := by
  induction keys with
  | nil => simp
  | cons k rest ih =>
    have hk := h k (by simp)
    have hr := ih (fun k hk => h k (by simp [hk]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def occupiedBuffers (key : α → Fin K) (B : ℕ) (xs : List α) : ℕ :=
  ((List.finRange K).map (fun k => (bufferedBuckets key B xs k).pending.length)).sum

/-- After every finite input prefix, all K pending buffers together use at
most K*B units. Completed blocks are on disk, not charged to memory. -/
theorem bucket_memory_bound (key : α → Fin K) (B : ℕ) (hB : 0 < B) (seen : List α) :
    occupiedBuffers key B seen ≤ K * B := by
  have h := sum_uniform_bound (List.finRange K)
    (fun k => (bufferedBuckets key B seen k).pending.length) B (by
      intro k _
      exact Nat.le_of_lt (buffered_bucket_valid key B hB seen k).2)
  simpa only [occupiedBuffers, List.length_finRange] using h

/-- The ordinary input/output streams are also written in actual blocks. -/
theorem pack_count_bound (B : ℕ) (hB : 0 < B) (xs : List α) :
    (pack B hB xs).length ≤ xs.length / B + 1 := by
  have h := (Nat.le_div_iff_mul_le hB).2 (Nat.le_of_lt (pack_capacity B hB xs).2)
  simpa only [Nat.add_div_right _ hB] using h

/-- Read the input stream once and write the bucket streams. -/
def distributionTransfers (key : α → Fin K) (B : ℕ) (hB : 0 < B) (xs : List α) : ℕ :=
  (pack B hB xs).length + flushCount key B xs

/-- Read each stored bucket block once, then pack the concatenated output. -/
def reconstructionTransfers (key : α → Fin K) (B : ℕ) (hB : 0 < B) (xs : List α) : ℕ :=
  flushCount key B xs + (pack B hB (bufferedCollect key B xs)).length

theorem distribution_transfer_bound
    (key : α → Fin K) (B : ℕ) (hB : 0 < B) (xs : List α) :
    distributionTransfers key B hB xs ≤ 2 * (xs.length / B) + K + 1 := by
  have hi := pack_count_bound B hB xs
  have hw := flush_count_bound key B hB xs
  unfold distributionTransfers
  omega

theorem reconstruction_transfer_bound
    (key : α → Fin K) (B : ℕ) (hB : 0 < B) (xs : List α) :
    reconstructionTransfers key B hB xs ≤ 2 * (xs.length / B) + K + 1 := by
  have hr := flush_count_bound key B hB xs
  have ho := pack_count_bound B hB (bufferedCollect key B xs)
  have hlen := (bufferedCollect_perm key B xs).length_eq
  rw [hlen] at ho
  unfold reconstructionTransfers
  omega

theorem complete_bucket_transfer_bound
    (key : α → Fin K) (B : ℕ) (hB : 0 < B) (xs : List α) :
    distributionTransfers key B hB xs + reconstructionTransfers key B hB xs ≤
      4 * (xs.length / B) + 2 * K + 2 := by
  have hd := distribution_transfer_bound key B hB xs
  have hr := reconstruction_transfer_bound key B hB xs
  omega

/-- Read only the head of the requested stream.  The schedule may interleave
the streams arbitrarily, but can never seek backwards within a stream. -/
def consumeSchedule (schedule : List (Fin K)) (streams : Fin K → List α) :
    Option (List α × (Fin K → List α)) :=
  match schedule with
  | [] => some ([], streams)
  | k :: later =>
    match streams k with
    | [] => none
    | a :: tail =>
      let next := fun j => if j = k then tail else streams j
      match consumeSchedule later next with
      | none => none
      | some (output, final) => some (a :: output, final)

/-- A fully proved head-only reconstruction algorithm: the key schedule of
any target list consumes its bucket streams and returns that exact list,
with every stream empty. -/
theorem consumeSchedule_filters (key : α → Fin K) (target : List α) :
    consumeSchedule (target.map key) (bucket key target) =
      some (target, fun _ => []) := by
  induction target with
  | nil => rfl
  | cons a rest ih =>
    have hhead : bucket key (a :: rest) (key a) = a :: bucket key rest (key a) := by
      simp [bucket]
    have hnext : (fun j => if j = key a then bucket key rest (key a)
        else bucket key (a :: rest) j) = bucket key rest := by
      funext j
      by_cases hj : j = key a
      · subst j
        simp
      · have hj' : key a ≠ j := Ne.symm hj
        simp [hj, hj', bucket]
    rw [List.map_cons, consumeSchedule, hhead]
    change (match consumeSchedule (rest.map key)
      (fun j => if j = key a then bucket key rest (key a)
        else bucket key (a :: rest) j) with
      | none => none
      | some (output, final) => some (a :: output, final)) = _
    rw [hnext, ih]

/-- If a desired reorder keeps each bucket's internal order, its known key
schedule reconstructs it by sequential reads alone. The stream equality is
the exact additional obligation when specializing to five-field addresses. -/
theorem consumeSchedule_reorder (key : α → Fin K) (input target : List α)
    (h : ∀ k, bucket key input k = bucket key target k) :
    consumeSchedule (target.map key) (bucket key input) =
      some (target, fun _ => []) := by
  have heq : bucket key input = bucket key target := funext h
  rw [heq]
  exact consumeSchedule_filters key target

/-- The streams emitted by the concrete buffered writer can be used directly
by the head-only reconstruction algorithm. -/
theorem consume_buffered_reorder (key : α → Fin K) (B : ℕ) (input target : List α)
    (h : ∀ k, bucket key input k = bucket key target k) :
    consumeSchedule (target.map key)
      (fun k => (bufferedBuckets key B input k).finish.flatten) =
      some (target, fun _ => []) := by
  simp_rw [buffered_bucket_correct]
  exact consumeSchedule_reorder key input target h

section AddressedRecords

variable {Prefix Field Gap Suffix Value : Type*}

/-- Addresses are explicit for this semantic theorem; the implementation
does not need to store a new address with every bit. -/
def exchangeRecord
    (r : Address.FullAddress Prefix Field Gap Suffix × Value) :=
  (Address.exchange r.1, r.2)

/-- All payloads and all spectator fields survive the concrete bucket pass.
The output consists of exactly the demanded destination/value pairs,
including duplicates; layout order is addressed by `consumeSchedule_reorder`. -/
theorem addressed_records_preserved
    (key : (Address.FullAddress Prefix Field Gap Suffix × Value) → Fin K)
    (B : ℕ) (xs : List (Address.FullAddress Prefix Field Gap Suffix × Value)) :
    ((bufferedCollect key B xs).map exchangeRecord).Perm (xs.map exchangeRecord) :=
  (bufferedCollect_perm key B xs).map exchangeRecord

theorem exchangeRecord_value
    (r : Address.FullAddress Prefix Field Gap Suffix × Value) :
    (exchangeRecord r).2 = r.2 := rfl

end AddressedRecords

section RectangularArray

variable {P Q G Z : ℕ} {Value : Type*}

abbrev RectAddress (P Q G Z : ℕ) :=
  Address.FullAddress (Fin P) (Fin Q) (Fin G) (Fin Z)

def rectRecord (F : RectAddress P Q G Z → Value)
    (p : Fin P) (h : Fin Q) (g : Fin G) (d : Fin Q) (z : Fin Z) :=
  let a : RectAddress P Q G Z := ⟨p, h, g, d, z⟩
  (a, F a)

def rectInput (F : RectAddress P Q G Z → Value) :=
  (List.finRange P).flatMap fun p =>
    (List.finRange Q).flatMap fun h =>
      (List.finRange G).flatMap fun g =>
        (List.finRange Q).flatMap fun d =>
          (List.finRange Z).map (rectRecord F p h g d)

/-- Source records listed in the destination's lexicographic order.
The output still carries source addresses until `exchangeRecord` is applied. -/
def rectTargetSources (F : RectAddress P Q G Z → Value) :=
  (List.finRange P).flatMap fun p =>
    (List.finRange Q).flatMap fun d =>
      (List.finRange G).flatMap fun g =>
        (List.finRange Q).flatMap fun h =>
          (List.finRange Z).map (rectRecord F p h g d)

def rectKey (r : RectAddress P Q G Z × Value) : Fin (Q * Q) :=
  finProdFinEquiv (r.1.high, r.1.low)

def rectFiber (F : RectAddress P Q G Z → Value) (h d : Fin Q) :=
  (List.finRange P).flatMap fun p =>
    (List.finRange G).flatMap fun g =>
      (List.finRange Z).map (rectRecord F p h g d)

private theorem flatMap_single_key {β γ : Type*} [DecidableEq β]
    (keys : List β) (hn : keys.Nodup) (k : β) (f : β → List γ) :
    (keys.flatMap fun j => if j = k then f j else []) =
      if k ∈ keys then f k else [] := by
  induction keys with
  | nil => simp
  | cons a rest ih =>
    have h := List.nodup_cons.mp hn
    by_cases hak : a = k
    · subst a
      simp [h.1, ih h.2]
    · simp [hak, ih h.2, Ne.symm hak]

private theorem flatMap_fin_single {n : ℕ} {β : Type*} (k : Fin n) (f : Fin n → List β) :
    ((List.finRange n).flatMap fun j => if j = k then f j else []) = f k := by
  simpa using flatMap_single_key (List.finRange n) (List.nodup_finRange n) k f

private theorem filter_rect_row (F : RectAddress P Q G Z → Value)
    (p : Fin P) (h h₀ : Fin Q) (g : Fin G) (d d₀ : Fin Q) :
    bucket rectKey ((List.finRange Z).map (rectRecord F p h g d))
      (finProdFinEquiv (h₀, d₀)) =
      if h = h₀ then if d = d₀ then (List.finRange Z).map (rectRecord F p h g d)
        else [] else [] := by
  by_cases hh : h = h₀ <;> by_cases hd : d = d₀ <;>
    simp [bucket, List.filter_map, Function.comp_def, rectRecord, rectKey, hh, hd]

private theorem bucket_flatMap {β : Type*} (key : α → Fin K)
    (xs : List β) (f : β → List α) (k : Fin K) :
    bucket key (xs.flatMap f) k = xs.flatMap (fun a => bucket key (f a) k) := by
  simp [bucket, List.filter_flatMap]

private theorem flatMap_uniform_if {β γ : Type*} (xs : List β)
    (p : Prop) [Decidable p] (f : β → List γ) :
    (xs.flatMap fun a => if p then f a else []) = if p then xs.flatMap f else [] := by
  by_cases h : p <;> simp [h]

/-- An (H,D) bucket contains exactly all spectator coordinates (p,g,z)
in their lexicographic order. -/
theorem rect_input_fiber (F : RectAddress P Q G Z → Value) (h d : Fin Q) :
    bucket rectKey (rectInput F) (finProdFinEquiv (h, d)) = rectFiber F h d := by
  simp only [rectInput, bucket_flatMap, filter_rect_row]
  simp_rw [flatMap_uniform_if, flatMap_fin_single]
  rfl

/-- Swapping the order of H and D leaves each (H,D) bucket's spectator
sequence unchanged, including all prefix, gap, and suffix coordinates. -/
theorem rect_target_fiber (F : RectAddress P Q G Z → Value) (h d : Fin Q) :
    bucket rectKey (rectTargetSources F) (finProdFinEquiv (h, d)) = rectFiber F h d := by
  simp only [rectTargetSources, bucket_flatMap, filter_rect_row]
  have hswap (h' d' : Fin Q) (xs : List (RectAddress P Q G Z × Value)) :
      (if h' = h then if d' = d then xs else [] else []) =
        (if d' = d then if h' = h then xs else [] else []) := by
    by_cases hh : h' = h <;> by_cases hd : d' = d <;> simp [hh, hd]
  simp_rw [hswap, flatMap_uniform_if, flatMap_fin_single]
  rfl

/-- Concrete complete-address reconstruction. Every requested read is from
the next position of its bucket; the output is exactly the desired order,
not merely a multiset equality. -/
theorem rectangular_reconstruction (F : RectAddress P Q G Z → Value) (B : ℕ) :
    consumeSchedule ((rectTargetSources F).map rectKey)
      (fun k => (bufferedBuckets rectKey B (rectInput F) k).finish.flatten) =
      some (rectTargetSources F, fun _ => []) := by
  apply consume_buffered_reorder
  intro k
  obtain ⟨⟨h, d⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [rect_input_fiber, rect_target_fiber]

theorem rect_input_length (F : RectAddress P Q G Z → Value) :
    (rectInput F).length = P * Q * G * Q * Z := by
  simp [rectInput, List.length_flatMap, Function.comp_def, List.map_const']
  ring

def rectangularExchange (F : RectAddress P Q G Z → Value) (B : ℕ) :
    Option (List (RectAddress P Q G Z × Value)) :=
  (consumeSchedule ((rectTargetSources F).map rectKey)
    (fun k => (bufferedBuckets rectKey B (rectInput F) k).finish.flatten)).map
      (fun result => result.1.map exchangeRecord)

def expectedExchangeOutput (F : RectAddress P Q G Z → Value) :=
  (List.finRange P).flatMap fun p =>
    (List.finRange Q).flatMap fun d =>
      (List.finRange G).flatMap fun g =>
        (List.finRange Q).flatMap fun h =>
          (List.finRange Z).map fun z =>
            ((⟨p, d, g, h, z⟩ : RectAddress P Q G Z),
              F ⟨p, h, g, d, z⟩)

/-- Exact input/output theorem for all five address fields and arbitrary
payload values. In particular, the output is in (p,D,g,H,z) order. -/
theorem rectangularExchange_correct (F : RectAddress P Q G Z → Value) (B : ℕ) :
    rectangularExchange F B = some (expectedExchangeOutput F) := by
  unfold rectangularExchange
  rw [rectangular_reconstruction]
  simp [rectTargetSources, expectedExchangeOutput, List.map_flatMap, List.map_map,
    Function.comp_def, rectRecord, exchangeRecord, Address.exchange]

theorem rectangular_buffer_memory (F : RectAddress P Q G Z → Value)
    (B : ℕ) (hB : 0 < B) :
    occupiedBuffers rectKey B (rectInput F) ≤ (Q * Q) * B :=
  bucket_memory_bound rectKey B hB (rectInput F)

end RectangularArray

end CSL.BucketMachine


