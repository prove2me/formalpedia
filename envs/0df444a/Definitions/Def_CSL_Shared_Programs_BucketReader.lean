-- Prove2me | Definitions.Def_CSL_Shared_Programs_BucketReader
-- name    : CSL_Shared_Programs_BucketReader
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:32:08.138059+00:00
-- url     : https://prove2.me/theorems/a37eb2cc-d932-48a1-b641-cbac71f95080
-- title:
--   Coded sorting library: Shared / Programs / BucketReader
-- statement:
--   Module `CodedSorting.Shared.Programs.BucketReader` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Sequential block readers for the head-only reconstruction schedule.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.BucketReader

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_BucketMachine

/-! Sequential block readers for the head-only reconstruction schedule. -/

namespace CSL.BucketReader

open BucketMachine

variable {α : Type*} {K : ℕ}

structure Reader (α : Type*) where
  disk : List (List α)
  pending : List α
  reads : ℕ

def Reader.contents (s : Reader α) := s.pending ++ s.disk.flatten

def Reader.Valid (B : ℕ) (s : Reader α) : Prop :=
  (∀ block ∈ s.disk, 0 < block.length ∧ block.length ≤ B) ∧ s.pending.length < B

def Reader.fromDisk (blocks : List (List α)) : Reader α := ⟨blocks, [], 0⟩

/-- Refill only when the current block is exhausted; every refill removes
exactly one block from the disk stream and increments `reads` once. -/
def Reader.pop (s : Reader α) : Option (α × Reader α) :=
  match s.pending with
  | a :: rest => some (a, ⟨s.disk, rest, s.reads⟩)
  | [] =>
    match s.disk with
    | [] => none
    | [] :: _ => none
    | (a :: rest) :: disk => some (a, ⟨disk, rest, s.reads + 1⟩)

theorem Reader.pop_contents (s t : Reader α) (a : α) (hp : s.pop = some (a, t)) :
    s.contents = a :: t.contents := by
  rcases s with ⟨disk, pending, reads⟩
  cases pending with
  | cons b rest => simp only [Reader.pop, Option.some.injEq, Prod.mk.injEq] at hp; rcases hp with ⟨rfl, rfl⟩; rfl
  | nil =>
    cases disk with
    | nil => simp [Reader.pop] at hp
    | cons block disk =>
      cases block with
      | nil => simp [Reader.pop] at hp
      | cons b rest =>
        simp only [Reader.pop, Option.some.injEq, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩
        simp [Reader.contents]

theorem Reader.pop_conservation (s t : Reader α) (a : α) (hp : s.pop = some (a, t)) :
    t.reads + t.disk.length = s.reads + s.disk.length := by
  rcases s with ⟨disk, pending, reads⟩
  cases pending with
  | cons b rest => simp only [Reader.pop, Option.some.injEq, Prod.mk.injEq] at hp; rcases hp with ⟨rfl, rfl⟩; rfl
  | nil =>
    cases disk with
    | nil => simp [Reader.pop] at hp
    | cons block disk =>
      cases block with
      | nil => simp [Reader.pop] at hp
      | cons b rest =>
        simp only [Reader.pop, Option.some.injEq, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem Reader.pop_valid (B : ℕ) (s t : Reader α) (a : α)
    (hs : s.Valid B) (hp : s.pop = some (a, t)) : t.Valid B := by
  rcases s with ⟨disk, pending, reads⟩
  cases pending with
  | cons b rest =>
    simp only [Reader.pop, Option.some.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩
    rcases hs with ⟨hd, hp⟩
    exact ⟨hd, by simpa using (Nat.lt_of_succ_lt hp)⟩
  | nil =>
    cases disk with
    | nil => simp [Reader.pop] at hp
    | cons block disk =>
      cases block with
      | nil => simp [Reader.pop] at hp
      | cons b rest =>
        simp only [Reader.pop, Option.some.injEq, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩
        refine ⟨fun block hm => hs.1 block (by simp [hm]), ?_⟩
        have h := (hs.1 (b :: rest) (by simp)).2
        simp only [List.length_cons] at h
        change rest.length < B
        omega

theorem Reader.pop_exists (B : ℕ) (s : Reader α) (hs : s.Valid B)
    (a : α) (tail : List α) (hc : s.contents = a :: tail) :
    ∃ t, s.pop = some (a, t) := by
  rcases s with ⟨disk, pending, reads⟩
  cases pending with
  | cons b rest =>
    simp only [Reader.contents, List.cons_append, List.cons.injEq] at hc
    rcases hc with ⟨rfl, _⟩
    exact ⟨_, rfl⟩
  | nil =>
    cases disk with
    | nil => simp [Reader.contents] at hc
    | cons block disk =>
      cases block with
      | nil => have h := (hs.1 [] (by simp)).1; simp at h
      | cons b rest =>
        simp only [Reader.contents, List.flatten_cons, List.nil_append, List.cons_append,
          List.cons.injEq] at hc
        rcases hc with ⟨rfl, _⟩
        exact ⟨_, rfl⟩

def readSchedule (schedule : List (Fin K)) (state : Fin K → Reader α) :
    Option (List α × (Fin K → Reader α)) :=
  match schedule with
  | [] => some ([], state)
  | k :: rest =>
    match (state k).pop with
    | none => none
    | some (a, t) =>
      match readSchedule rest (fun j => if j = k then t else state j) with
      | none => none
      | some (out, final) => some (a :: out, final)

/-- The buffered implementation realizes the head-only list algorithm.
The per-bucket conservation law counts every actual block refill. -/
theorem readSchedule_realizes (B : ℕ) (schedule : List (Fin K))
    (state : Fin K → Reader α) (hs : ∀ k, (state k).Valid B)
    (out : List α) (streams : Fin K → List α)
    (hp : consumeSchedule schedule (fun k => (state k).contents) = some (out, streams)) :
    ∃ final, readSchedule schedule state = some (out, final) ∧
      (∀ k, (final k).Valid B) ∧
      (∀ k, (final k).contents = streams k) ∧
      (∀ k, (final k).reads + (final k).disk.length =
        (state k).reads + (state k).disk.length) := by
  induction schedule generalizing state out streams with
  | nil =>
    simp only [consumeSchedule, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨state, rfl, hs, fun _ => rfl, fun _ => rfl⟩
  | cons k rest ih =>
    cases hc : (state k).contents with
    | nil => simp [consumeSchedule, hc] at hp
    | cons a tail =>
      obtain ⟨t, hpop⟩ := Reader.pop_exists B (state k) (hs k) a tail hc
      have ht : t.contents = tail := by
        have hh := Reader.pop_contents (state k) t a hpop
        rw [hc] at hh
        exact (List.cons.inj hh).2.symm
      let next := fun j => if j = k then t else state j
      have hv : ∀ j, (next j).Valid B := by
        intro j
        by_cases hj : j = k
        · subst j
          simpa [next] using Reader.pop_valid B (state k) t a (hs k) hpop
        · simpa [next, hj] using hs j
      have hn : (fun j => (next j).contents) =
          (fun j => if j = k then tail else (state j).contents) := by
        funext j
        by_cases hj : j = k <;> simp [next, hj, ht]
      cases hr : consumeSchedule rest
          (fun j => if j = k then tail else (state j).contents) with
      | none => simp [consumeSchedule, hc, hr] at hp
      | some result =>
        rcases result with ⟨out', streams'⟩
        simp only [consumeSchedule, hc, hr, Option.some.injEq, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩
        have hr' : consumeSchedule rest (fun j => (next j).contents) =
            some (out', streams') := by rw [hn]; exact hr
        obtain ⟨final, hf, hfv, hfc, hcount⟩ := ih next hv out' streams' hr'
        refine ⟨final, ?_, hfv, hfc, ?_⟩
        · simp only [readSchedule, hpop]
          change (match readSchedule rest next with
            | none => none
            | some (out, final) => some (a :: out, final)) = _
          rw [hf]
        · intro j
          rw [hcount j]
          by_cases hj : j = k
          · subst j
            simpa [next] using Reader.pop_conservation (state k) t a hpop
          · simp [next, hj]

theorem writer_finish_valid (B : ℕ) (hB : 0 < B) (s : Writer α) (hs : s.Valid B) :
    (Reader.fromDisk s.finish).Valid B := by
  refine ⟨?_, hB⟩
  intro block hb
  change block ∈ s.finish at hb
  by_cases he : s.pending = []
  · simp [Writer.finish, he] at hb
    rw [hs.1 block hb]
    exact ⟨hB, le_rfl⟩
  · have hempty : s.pending.isEmpty = false := by simpa using he
    simp only [Writer.finish, hempty, Bool.false_eq_true, ↓reduceIte,
      List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · rw [hs.1 block hb]
      exact ⟨hB, le_rfl⟩
    · exact ⟨List.length_pos_iff.mpr he, Nat.le_of_lt hs.2⟩

def initialReaders (key : α → Fin K) (B : ℕ) (xs : List α) : Fin K → Reader α :=
  fun k => Reader.fromDisk (bufferedBuckets key B xs k).finish

theorem initialReaders_contents (key : α → Fin K) (B : ℕ) (xs : List α) (k : Fin K) :
    (initialReaders key B xs k).contents = bucket key xs k := by
  simpa [initialReaders, Reader.fromDisk, Reader.contents] using buffered_bucket_correct key B xs k

theorem initialReaders_valid (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (xs : List α) (k : Fin K) : (initialReaders key B xs k).Valid B :=
  writer_finish_valid B hB _ (buffered_bucket_valid key B hB xs k)

theorem Reader.empty_contents_disk (B : ℕ) (s : Reader α) (hs : s.Valid B)
    (he : s.contents = []) : s.disk = [] := by
  have hf : s.disk.flatten = [] := (List.append_eq_nil_iff.mp he).2
  cases hd : s.disk with
  | nil => rfl
  | cons block rest =>
    have hp := (hs.1 block (by simp [hd])).1
    simp [hd] at hf
    rcases hf with ⟨rfl, _⟩
    simp at hp

def readCount (state : Fin K → Reader α) : ℕ :=
  ((List.finRange K).map (fun k => (state k).reads)).sum

def occupiedReaders (state : Fin K → Reader α) : ℕ :=
  ((List.finRange K).map (fun k => (state k).pending.length)).sum

private theorem sum_capacity {β : Type*} (keys : List β) (f : β → ℕ) (B : ℕ)
    (h : ∀ k ∈ keys, f k ≤ B) : (keys.map f).sum ≤ keys.length * B := by
  induction keys with
  | nil => simp
  | cons k rest ih =>
    have hk := h k (by simp)
    have hr := ih (fun k hk => h k (by simp [hk]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem reader_memory (B : ℕ) (state : Fin K → Reader α)
    (hs : ∀ k, (state k).Valid B) : occupiedReaders state ≤ K * B := by
  have h := sum_capacity (List.finRange K) (fun k => (state k).pending.length) B
    (fun k _ => Nat.le_of_lt (hs k).2)
  simpa only [occupiedReaders, List.length_finRange] using h

/-- Every successful prefix of the physical head schedule preserves the
reader-buffer invariant, independently of any target-layout specification. -/
theorem readSchedule_valid (B : ℕ) (schedule : List (Fin K))
    (initial final : Fin K → Reader α) (output : List α)
    (hi : ∀ k, (initial k).Valid B)
    (he : readSchedule schedule initial = some (output, final)) :
    ∀ k, (final k).Valid B := by
  induction schedule generalizing initial final output with
  | nil =>
    simp only [readSchedule, Option.some.injEq, Prod.mk.injEq] at he
    exact he.2 ▸ hi
  | cons k rest ih =>
    unfold readSchedule at he
    cases hp : (initial k).pop with
    | none => simp [hp] at he
    | some pair =>
      obtain ⟨a, reader⟩ := pair
      let next := fun j => if j = k then reader else initial j
      have hn : ∀ j, (next j).Valid B := by
        intro j
        by_cases hj : j = k
        · subst j
          simpa [next] using Reader.pop_valid B _ _ _ (hi k) hp
        · simpa [next, hj] using hi j
      simp only [hp] at he
      change (match readSchedule rest next with
        | none => none
        | some (out, state) => some (a :: out, state)) = some (output, final) at he
      cases ht : readSchedule rest next with
      | none => simp [ht] at he
      | some pair =>
        obtain ⟨tail, finalState⟩ := pair
        have hv := ih next finalState tail hn ht
        simp only [ht, Option.some.injEq, Prod.mk.injEq] at he
        exact he.2 ▸ hv

theorem readSchedule_memory (B : ℕ) (schedule : List (Fin K))
    (initial final : Fin K → Reader α) (output : List α)
    (hi : ∀ k, (initial k).Valid B)
    (he : readSchedule schedule initial = some (output, final)) :
    occupiedReaders final ≤ K * B :=
  reader_memory B final (readSchedule_valid B schedule initial final output hi he)

/-- Complete refinement from the abstract head schedule to block reads.
The exact read count equals the number of blocks actually emitted earlier. -/
theorem buffered_reconstruction (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (input target : List α) (h : ∀ k, bucket key input k = bucket key target k) :
    ∃ final, readSchedule (target.map key) (initialReaders key B input) = some (target, final) ∧
      readCount final = flushCount key B input ∧ occupiedReaders final ≤ K * B := by
  have hp : consumeSchedule (target.map key)
      (fun k => (initialReaders key B input k).contents) = some (target, fun _ => []) := by
    simp_rw [initialReaders_contents]
    exact consumeSchedule_reorder key input target h
  obtain ⟨final, hf, hv, hc, hcount⟩ := readSchedule_realizes B (target.map key)
    (initialReaders key B input) (initialReaders_valid key B hB input) target _ hp
  refine ⟨final, hf, ?_, reader_memory B final hv⟩
  have hr (k : Fin K) : (final k).reads = (bufferedBuckets key B input k).finish.length := by
    have hd := Reader.empty_contents_disk B (final k) (hv k) (hc k)
    have hh := hcount k
    rw [hd] at hh
    simpa [initialReaders, Reader.fromDisk] using hh
  simp only [readCount, flushCount, hr]

theorem reorder_length (key : α → Fin K) (input target : List α)
    (h : ∀ k, bucket key input k = bucket key target k) : target.length = input.length := by
  have heq : collect key input = collect key target := by
    unfold collect
    rw [funext h]
  have hi := collect_length key input
  rw [heq, collect_length] at hi
  exact hi

def completeTransfers (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (input target : List α) (final : Fin K → Reader α) : ℕ :=
  (pack B hB input).length + flushCount key B input +
    readCount final + (pack B hB target).length

/-- This cost counts actual input block reads, bucket flushes, scheduled
refills, and final output writes. It contains no asymptotic cost premise. -/
theorem complete_reconstruction_bound (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (input target : List α) (h : ∀ k, bucket key input k = bucket key target k) :
    ∃ final, readSchedule (target.map key) (initialReaders key B input) = some (target, final) ∧
      completeTransfers key B hB input target final ≤ 4 * (input.length / B) + 2 * K + 2 ∧
      occupiedReaders final ≤ K * B := by
  obtain ⟨final, hf, hr, hm⟩ := buffered_reconstruction key B hB input target h
  refine ⟨final, hf, ?_, hm⟩
  have hi := pack_count_bound B hB input
  have ho := pack_count_bound B hB target
  have hw := flush_count_bound key B hB input
  rw [reorder_length key input target h] at ho
  unfold completeTransfers
  rw [hr]
  omega

/-- Section 5.3's complete rectangular case: all five address coordinates,
all payload values, and the physical bucket-block transfers are included. -/
theorem rectangular_block_reconstruction {P Q G Z : ℕ} {Value : Type*}
    (F : RectAddress P Q G Z → Value) (B : ℕ) (hB : 0 < B) :
    ∃ final, readSchedule ((rectTargetSources F).map rectKey)
        (initialReaders rectKey B (rectInput F)) = some (rectTargetSources F, final) ∧
      completeTransfers rectKey B hB (rectInput F) (rectTargetSources F) final ≤
        4 * ((P * Q * G * Q * Z) / B) + 2 * (Q * Q) + 2 ∧
      occupiedReaders final ≤ (Q * Q) * B := by
  have hf (k : Fin (Q * Q)) : bucket rectKey (rectInput F) k =
      bucket rectKey (rectTargetSources F) k := by
    obtain ⟨⟨h, d⟩, rfl⟩ := finProdFinEquiv.surjective k
    rw [rect_input_fiber, rect_target_fiber]
  simpa only [rect_input_length] using
    complete_reconstruction_bound rectKey B hB (rectInput F) (rectTargetSources F) hf

end CSL.BucketReader


