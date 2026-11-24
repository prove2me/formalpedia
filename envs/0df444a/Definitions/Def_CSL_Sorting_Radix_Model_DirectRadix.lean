-- Prove2me | Definitions.Def_CSL_Sorting_Radix_Model_DirectRadix
-- name    : CSL_Sorting_Radix_Model_DirectRadix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:24:39.484801+00:00
-- url     : https://prove2.me/theorems/f3036822-5809-414a-a677-17fe1bc8a4df
-- title:
--   Coded sorting library: Sorting / Radix / Model / DirectRadix
-- statement:
--   Module `CodedSorting.Sorting.Radix.Model.DirectRadix` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Section 7.3: stable direct radix passes with an external linked directory.
--   The input is scanned backwards and prepended to disk lists. No array of K
--   bucket heads is held in RAM. A directory cell occupies the prefix of its own
--   physical block; the spare space is permitted polynomial scratch space.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Radix.Model.DirectRadix

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_Radix_Model_ExternalMSD
import Definitions.Def_CSL_Shared_Programs_Normalization
import Mathlib.Data.Nat.Log

/-! Section 7.3: stable direct radix passes with an external linked directory.
The input is scanned backwards and prepended to disk lists. No array of K
bucket heads is held in RAM. A directory cell occupies the prefix of its own
physical block; the spare space is permitted polynomial scratch space. -/
namespace CSL.DirectRadix
open BucketMachine
variable {α : Type*} {n K : ℕ}

abbrev Pointer (n : ℕ) := Option (Fin n)

structure Heap (n K : ℕ) where
  head : Fin K → Pointer n
  next : Fin n → Pointer n

def Heap.empty : Heap n K := ⟨fun _ => none, fun _ => none⟩

/-- A linked chain is a disk representation of a list of input positions. -/
def Chain (links : Fin n → Pointer n) : Pointer n → List (Fin n) → Prop
  | p, [] => p = none
  | p, i :: rest => p = some i ∧ Chain links (links i) rest

def Represents (heap : Heap n K) (lists : Fin K → List (Fin n)) : Prop :=
  ∀ k, Chain heap.next (heap.head k) (lists k)

theorem chain_update_fresh (links : Fin n → Pointer n) (p : Pointer n)
    (ids : List (Fin n)) (i : Fin n) (target : Pointer n)
    (hf : i ∉ ids) (hc : Chain links p ids) :
    Chain (Function.update links i target) p ids := by
  induction ids generalizing p with
  | nil => exact hc
  | cons j rest ih =>
    obtain ⟨hp, ht⟩ := hc
    have hji : j ≠ i := by intro h; subst j; simp at hf
    refine ⟨hp, ?_⟩
    rw [Function.update_of_ne hji]
    exact ih (links j) (by intro hx; exact hf (List.mem_cons_of_mem _ hx)) ht

/-- One head read and two writes: initialize next[i], then replace head[k]. -/
def prepend (key : Fin n → Fin K) (i : Fin n) (heap : Heap n K) : Heap n K :=
  ⟨Function.update heap.head (key i) (some i),
    Function.update heap.next i (heap.head (key i))⟩

theorem prepend_represents (key : Fin n → Fin K) (i : Fin n) (heap : Heap n K)
    (lists : Fin K → List (Fin n)) (hr : Represents heap lists)
    (hf : ∀ k, i ∉ lists k) :
    Represents (prepend key i heap) (fun k => if key i = k then i :: lists k else lists k) := by
  intro k
  by_cases hk : key i = k
  · subst k
    simp only [if_pos rfl]
    change ((prepend key i heap).head (key i) = some i) ∧ _
    refine ⟨by simp [prepend], ?_⟩
    change Chain (Function.update heap.next i (heap.head (key i)))
      ((Function.update heap.next i (heap.head (key i))) i) (lists (key i))
    rw [Function.update_self]
    exact chain_update_fresh heap.next _ _ i _ (hf _) (hr _)
  · have hki : k ≠ key i := Ne.symm hk
    simp only [hk, ↓reduceIte]
    change Chain (Function.update heap.next i (heap.head (key i)))
      ((Function.update heap.head (key i) (some i)) k) (lists k)
    rw [Function.update_of_ne hki]
    exact chain_update_fresh heap.next _ _ i _ (hf k) (hr k)

/-- Constant-state, backwards-input construction. Only a current position,
record, bucket number and pointer are needed by the operational loop. -/
def build (key : Fin n → Fin K) (ids : List (Fin n)) : Heap n K :=
  ids.reverse.foldl (fun heap i => prepend key i heap) Heap.empty

theorem build_cons (key : Fin n → Fin K) (i : Fin n) (ids : List (Fin n)) :
    build key (i :: ids) = prepend key i (build key ids) := by
  simp [build, List.reverse_cons, List.foldl_append]

theorem build_represents (key : Fin n → Fin K) (ids : List (Fin n)) (hd : ids.Nodup) :
    Represents (build key ids) (bucket key ids) := by
  induction ids with
  | nil => intro k; simp [build, Heap.empty, bucket, Chain]
  | cons i rest ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hd
    have hr := ih htail
    have hf (k : Fin K) : i ∉ bucket key rest k := by
      intro h
      exact hnot ((mem_bucket key rest k i).mp h).1
    have hp := prepend_represents key i (build key rest) (bucket key rest) hr hf
    rw [build_cons]
    intro k
    have h := hp k
    by_cases hk : key i = k <;> simpa [bucket, hk] using h

/-- A physical node traversal reads a next pointer exactly once per record. -/
def follow (links : Fin n → Pointer n) : ℕ → Pointer n → Option (List (Fin n))
  | _, none => some []
  | 0, some _ => none
  | fuel + 1, some i => (follow links fuel (links i)).map (List.cons i)

theorem follow_correct (links : Fin n → Pointer n) (ids : List (Fin n))
    (p : Pointer n) (hc : Chain links p ids) (fuel : ℕ) (hf : ids.length ≤ fuel) :
    follow links fuel p = some ids := by
  induction ids generalizing p fuel with
  | nil => rw [show p = none from hc]; cases fuel <;> rfl
  | cons i rest ih =>
    obtain ⟨rfl, htail⟩ := hc
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      simp only [follow, ih _ htail _ (by simpa using hf)]
      rfl

/-- A pass actually follows the externally stored head/next chains. -/
def passIndices (key : Fin n → Fin K) : Option (List (Fin n)) :=
  let heap := build key (List.finRange n)
  ((List.finRange K).mapM (fun k => follow heap.next n (heap.head k))).map List.flatten

theorem passIndices_correct (key : Fin n → Fin K) :
    passIndices key = some (collect key (List.finRange n)) := by
  let heap := build key (List.finRange n)
  have hc := build_represents key (List.finRange n) (List.nodup_finRange n)
  have hf (k : Fin K) : follow heap.next n (heap.head k) = some (bucket key (List.finRange n) k) := by
    apply follow_correct _ _ _ (hc k)
    have h := (bucket_sublist key (List.finRange n) k).length_le
    simpa using h
  simp only [passIndices]
  change (((List.finRange K).mapM fun k => follow heap.next n (heap.head k))).map List.flatten = _
  simp_rw [hf]
  have hm : ∀ keys : List (Fin K),
      keys.mapM (fun k => some (bucket key (List.finRange n) k)) =
        some (keys.map (bucket key (List.finRange n))) := by
    intro keys
    induction keys with
    | nil => rfl
    | cons k rest ih => simp [List.mapM_cons, ih]
  rw [hm]
  rfl

/-- The heap and output are on disk. Only one record and one pointer are
resident here; loop indices are separate constant-size control registers.
`transfers` is a ghost counter, not an additional unbounded RAM register. -/
structure Machine (α : Type*) (n K : ℕ) where
  heap : Heap n K
  record : α
  pointer : Pointer n
  output : List α
  transfers : ℕ

def readInput (input : Fin n → α) (i : Fin n) (s : Machine α n K) : Machine α n K :=
  { s with record := input i, transfers := s.transfers + 1 }

def readHead (k : Fin K) (s : Machine α n K) : Machine α n K :=
  { s with pointer := s.heap.head k, transfers := s.transfers + 1 }

def readNext (i : Fin n) (s : Machine α n K) : Machine α n K :=
  { s with pointer := s.heap.next i, transfers := s.transfers + 1 }

def writeHead (k : Fin K) (s : Machine α n K) : Machine α n K :=
  { s with heap := ⟨Function.update s.heap.head k s.pointer, s.heap.next⟩, transfers := s.transfers + 1 }

def writeNext (i : Fin n) (s : Machine α n K) : Machine α n K :=
  { s with heap := ⟨s.heap.head, Function.update s.heap.next i s.pointer⟩, transfers := s.transfers + 1 }

/-- Append one word to a separately addressed output cell. The output list
is disk state and is not retained as a resident RAM list. -/
def emit (s : Machine α n K) : Machine α n K :=
  { s with output := s.output ++ [s.record], transfers := s.transfers + 1 }

/-- Key extraction uses the fetched record; accessing the bucket directory
requires its own explicit read, followed by two explicit pointer writes. -/
def insertRecord (input : Fin n → α) (key : α → Fin K) (i : Fin n)
    (s : Machine α n K) : Machine α n K :=
  let loaded := readInput input i s
  let k := key loaded.record
  let headed := readHead k loaded
  let linked := writeNext i headed
  writeHead k { linked with pointer := some i }

theorem insertRecord_heap (input : Fin n → α) (key : α → Fin K) (i : Fin n)
    (s : Machine α n K) :
    (insertRecord input key i s).heap = prepend (fun j => key (input j)) i s.heap := by
  rfl

theorem insertRecord_transfers (input : Fin n → α) (key : α → Fin K) (i : Fin n)
    (s : Machine α n K) : (insertRecord input key i s).transfers = s.transfers + 4 := by
  simp [insertRecord, readInput, readHead, writeNext, writeHead, Nat.add_assoc]

theorem insertRecord_output (input : Fin n → α) (key : α → Fin K) (i : Fin n)
    (s : Machine α n K) : (insertRecord input key i s).output = s.output := rfl

def clearHead (k : Fin K) (s : Machine α n K) : Machine α n K :=
  writeHead k {s with pointer := none}

def initializeDirectory [Inhabited α] : Machine α n K :=
  (List.finRange K).foldl (fun s k => clearHead k s) ⟨Heap.empty, default, none, [], 0⟩

theorem clear_empty_fold [Inhabited α] (keys : List (Fin K)) (count : ℕ) :
    keys.foldl (fun s k => clearHead k s)
      (⟨Heap.empty, default, none, [], count⟩ : Machine α n K) =
      ⟨Heap.empty, default, none, [], count + keys.length⟩ := by
  induction keys generalizing count with
  | nil => simp
  | cons k rest ih =>
    have hstep : clearHead k (⟨Heap.empty, default, none, [], count⟩ : Machine α n K) =
        ⟨Heap.empty, default, none, [], count + 1⟩ := by
      simp [clearHead, writeHead, Heap.empty, Function.update_eq_self]
    simp only [List.foldl_cons, hstep, ih, List.length_cons]
    congr 1
    omega

theorem initializeDirectory_eq [Inhabited α] : (initializeDirectory : Machine α n K) =
    ⟨Heap.empty, default, none, [], K⟩ := by
  simpa [initializeDirectory] using clear_empty_fold (α := α) (n := n) (List.finRange K) 0

def buildMachine [Inhabited α] (input : Fin n → α) (key : α → Fin K)
    (ids : List (Fin n)) : Machine α n K :=
  ids.reverse.foldl (fun s i => insertRecord input key i s) initializeDirectory

theorem buildMachine_cons [Inhabited α] (input : Fin n → α) (key : α → Fin K)
    (i : Fin n) (ids : List (Fin n)) :
    buildMachine input key (i :: ids) = insertRecord input key i (buildMachine input key ids) := by
  simp [buildMachine, List.reverse_cons, List.foldl_append]

theorem buildMachine_spec [Inhabited α] (input : Fin n → α) (key : α → Fin K)
    (ids : List (Fin n)) :
    (buildMachine input key ids).heap = build (fun i => key (input i)) ids ∧
      (buildMachine input key ids).output = [] ∧
      (buildMachine input key ids).transfers = K + 4 * ids.length := by
  induction ids with
  | nil => simp [buildMachine, build, initializeDirectory_eq, Heap.empty]
  | cons i rest ih =>
    rw [buildMachine_cons]
    simp only [insertRecord_heap, insertRecord_output, insertRecord_transfers,
      build_cons, ih.1, ih.2.1, ih.2.2, List.length_cons]
    exact ⟨trivial, trivial, by omega⟩

/-- Actual traversal: fetch the record, write it to the next output cell,
then fetch its next pointer. Termination is bounded by the input length. -/
def walk (input : Fin n → α) : ℕ → Machine α n K → Option (Machine α n K)
  | fuel, s =>
      match s.pointer with
      | none => some s
      | some i =>
          match fuel with
          | 0 => none
          | fuel + 1 => walk input fuel (readNext i (emit (readInput input i s)))

/-- One chain costs exactly three data/pointer transfers per record. -/
theorem walk_correct (input : Fin n → α) (ids : List (Fin n))
    (s : Machine α n K) (hc : Chain s.heap.next s.pointer ids)
    (fuel : ℕ) (hf : ids.length ≤ fuel) :
    ∃ t, walk input fuel s = some t ∧ t.heap = s.heap ∧
      t.output = s.output ++ ids.map input ∧
      t.transfers = s.transfers + 3 * ids.length := by
  induction ids generalizing s fuel with
  | nil =>
    have hp : s.pointer = none := hc
    refine ⟨s, ?_, rfl, by simp, by simp⟩
    cases fuel <;> simp [walk, hp]
  | cons i rest ih =>
    obtain ⟨hp, htail⟩ := hc
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      let next := readNext i (emit (readInput input i s))
      have hn : Chain next.heap.next next.pointer rest := htail
      obtain ⟨t, he, hh, ho, ht⟩ := ih next hn fuel (by simpa using hf)
      refine ⟨t, ?_, hh, ?_, ?_⟩
      · rw [walk, hp]
        exact he
      · rw [ho]
        simp [next, readNext, emit, readInput, List.append_assoc]
      · rw [ht]
        simp [next, readNext, emit, readInput, List.length_cons]
        omega

/-- Each bucket incurs its explicit directory read, including empty buckets. -/
def gatherMachine (input : Fin n → α) : List (Fin K) → Machine α n K → Option (Machine α n K)
  | [], s => some s
  | k :: rest, s =>
      match walk input n (readHead k s) with
      | none => none
      | some t => gatherMachine input rest t

theorem gatherMachine_correct (input : Fin n → α) (keys : List (Fin K))
    (lists : Fin K → List (Fin n)) (s : Machine α n K)
    (hr : Represents s.heap lists) (hlen : ∀ k, (lists k).length ≤ n) :
    ∃ t, gatherMachine input keys s = some t ∧ t.heap = s.heap ∧
      t.output = s.output ++ (keys.flatMap lists).map input ∧
      t.transfers = s.transfers + keys.length + 3 * (keys.flatMap lists).length := by
  induction keys generalizing s with
  | nil => exact ⟨s, rfl, rfl, by simp, by simp⟩
  | cons k rest ih =>
    obtain ⟨mid, he, hh, ho, ht⟩ := walk_correct input (lists k) (readHead k s) (hr k) n (hlen k)
    have hmid : Represents mid.heap lists := by rw [hh]; exact hr
    obtain ⟨t, he', hh', ho', ht'⟩ := ih mid hmid
    refine ⟨t, ?_, hh'.trans hh, ?_, ?_⟩
    · simp [gatherMachine, he, he']
    · rw [ho', ho]
      simp [readHead, List.flatMap_cons, List.map_append, List.append_assoc]
    · rw [ht', ht]
      simp [readHead, List.flatMap_cons, List.length_append]
      omega

/-- Payload movement commutes with stable bucket selection. -/
theorem bucket_map {β : Type*} (key : β → Fin K) (f : α → β)
    (xs : List α) (k : Fin K) :
    bucket key (xs.map f) k = (bucket (fun x => key (f x)) xs k).map f := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [bucket] at ih
    by_cases h : key (f x) = k <;> simp [bucket, h, ih]

theorem collect_map {β : Type*} (key : β → Fin K) (f : α → β) (xs : List α) :
    collect key (xs.map f) = (collect (fun x => key (f x)) xs).map f := by
  simp only [collect, List.map_flatMap]
  apply List.flatMap_congr
  intro k _
  exact bucket_map key f xs k

/-- One complete direct pass; no K-entry directory is kept in memory. -/
def pass [Inhabited α] (key : α → Fin K) (xs : List α) : Option (List α × ℕ) :=
  let input := xs.get
  let built := buildMachine input key (List.finRange xs.length)
  (gatherMachine input (List.finRange K) built).map fun final => (final.output, final.transfers)

/-- Exact transfer accounting includes empty-directory initialization and
reads, every data fetch, every next-pointer access, and output writes. -/
theorem pass_correct [Inhabited α] (key : α → Fin K) (xs : List α) :
    pass key xs = some (collect key xs, 7 * xs.length + 2 * K) := by
  let input := xs.get
  let ids := List.finRange xs.length
  let built := buildMachine input key ids
  let lists := bucket (fun i => key (input i)) ids
  have hb := buildMachine_spec input key ids
  have hr : Represents built.heap lists := by
    rw [show built.heap = build (fun i => key (input i)) ids from hb.1]
    exact build_represents _ _ (List.nodup_finRange _)
  have hlen (k : Fin K) : (lists k).length ≤ xs.length := by
    simpa [lists, ids] using (bucket_sublist (fun i => key (input i)) ids k).length_le
  obtain ⟨final, he, _, ho, ht⟩ := gatherMachine_correct input (List.finRange K) lists built hr hlen
  have hl : ((List.finRange K).flatMap lists).length = xs.length := by
    simpa [lists, ids, collect] using collect_length (fun i => key (input i)) ids
  have hm : ((List.finRange K).flatMap lists).map input = collect key xs := by
    have h := collect_map key input ids
    rw [show ids.map input = xs from List.finRange_map_get xs] at h
    exact h.symm
  have hout : final.output = collect key xs := by
    rw [ho, hb.2.1, List.nil_append, hm]
  have hcost : final.transfers = 7 * xs.length + 2 * K := by
    rw [ht, hb.2.2, hl]
    simp only [ids, List.length_finRange]
    omega
  change (gatherMachine input (List.finRange K) built).map _ = _
  rw [he]
  simp [hout, hcost]

/-- Least-significant-digit radix sorting uses the stable order proved for
the direct linked-list pass. There is no local-sort oracle. -/
def lsd (base : ℕ) (hb : 0 < base) : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | rounds + 1, xs => collect (MSD.digit base hb rounds) (lsd base hb rounds xs)

theorem lsd_perm (base : ℕ) (hb : 0 < base) (rounds : ℕ) (xs : List ℕ) :
    (lsd base hb rounds xs).Perm xs := by
  induction rounds with
  | zero => exact List.Perm.refl xs
  | succ rounds ih => exact (collect_perm _ _).trans ih

theorem lsd_pairwise_remainder (base : ℕ) (hb : 0 < base) (rounds : ℕ) (xs : List ℕ) :
    (lsd base hb rounds xs).Pairwise (fun x y => x % base ^ rounds ≤ y % base ^ rounds) := by
  induction rounds with
  | zero =>
    simp only [lsd, pow_zero, Nat.mod_one]
    exact List.pairwise_of_forall (by intro a b; exact Nat.le_refl 0)
  | succ rounds ih =>
    let child := bucket (MSD.digit base hb rounds) (lsd base hb rounds xs)
    have hmem (k : Fin base) (x : ℕ) (hx : x ∈ child k) : MSD.digit base hb rounds x = k :=
      ((mem_bucket _ _ _ _).mp hx).2
    change ((List.finRange base).map child).flatten.Pairwise _
    apply BucketOrder.pairwise_flatten_of_buckets
    · intro ys hys
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hys
      have hsub := ih.sublist (bucket_sublist (MSD.digit base hb rounds) (lsd base hb rounds xs) k)
      apply hsub.imp_of_mem
      intro x y hx hy hxy
      exact MSD.same_digit_order base hb rounds x y ((hmem k x hx).trans (hmem k y hy).symm) hxy
    · apply (List.pairwise_lt_finRange base).map child
      intro k l hkl x hx y hy
      apply MSD.different_digit_order base hb rounds x y
      rw [hmem k x hx, hmem l y hy]
      exact hkl

theorem lsd_correct (base : ℕ) (hb : 0 < base) (rounds : ℕ) (xs : List ℕ)
    (hbound : ∀ x ∈ xs, x < base ^ rounds) :
    (lsd base hb rounds xs).Perm xs ∧ (lsd base hb rounds xs).Pairwise (· ≤ ·) := by
  have hp := lsd_perm base hb rounds xs
  refine ⟨hp, ?_⟩
  apply (lsd_pairwise_remainder base hb rounds xs).imp_of_mem
  intro x y hx hy hxy
  simpa only [Nat.mod_eq_of_lt (hbound x (hp.mem_iff.mp hx)),
    Nat.mod_eq_of_lt (hbound y (hp.mem_iff.mp hy))] using hxy

/-- Each round executes the linked-list machine and sums its returned
transfer counter. Previous output becomes the next read-only input file. -/
def radixMachine (base : ℕ) (hb : 0 < base) : ℕ → List ℕ → Option (List ℕ × ℕ)
  | 0, xs => some (xs, 0)
  | rounds + 1, xs => do
      let (previous, cost) ← radixMachine base hb rounds xs
      let (output, passCost) ← pass (MSD.digit base hb rounds) previous
      pure (output, cost + passCost)

theorem radixMachine_spec (base : ℕ) (hb : 0 < base) (rounds : ℕ) (xs : List ℕ) :
    radixMachine base hb rounds xs =
      some (lsd base hb rounds xs, rounds * (7 * xs.length + 2 * base)) := by
  induction rounds with
  | zero => simp [radixMachine, lsd]
  | succ rounds ih =>
    simp [radixMachine, ih, pass_correct, lsd,
      (lsd_perm base hb rounds xs).length_eq, Nat.succ_mul]

/-- For N-bounded radix and a fixed polynomial universe, the actual direct
machine uses exactly 9 c N transfers, irrespective of the physical B. -/
theorem polynomial_universe_sort (c : ℕ) (xs : List ℕ) (hn : 0 < xs.length)
    (hbound : ∀ x ∈ xs, x < xs.length ^ c) :
    ∃ output, radixMachine xs.length hn c xs = some (output, 9 * c * xs.length) ∧
      output.Perm xs ∧ output.Pairwise (· ≤ ·) := by
  refine ⟨lsd xs.length hn c xs, ?_, lsd_correct _ hn c xs hbound⟩
  rw [radixMachine_spec]
  congr 2
  ring

/-- The ceiling power of two is at most twice N, hence at most N² for N≥2. -/
theorem ceiling_power_le_square (N : ℕ) (hN : 2 ≤ N) :
    2 ^ Nat.clog 2 N ≤ N ^ 2 := by
  have hc : 0 < Nat.clog 2 N := Nat.clog_pos (by decide) hN
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < N)
  have he : Nat.clog 2 N = (Nat.clog 2 N).pred + 1 := (Nat.succ_pred_eq_of_pos hc).symm
  calc
    2 ^ Nat.clog 2 N = 2 ^ (Nat.clog 2 N).pred * 2 := by conv_lhs => rw [he, pow_succ]
    _ ≤ N * 2 := Nat.mul_le_mul_right 2 (Nat.le_of_lt hp)
    _ ≤ N ^ 2 := by nlinarith

/-- A w-bit universe with w≤c ceil(log₂ N) lies inside N^(2c).
The bound is exact integer arithmetic, with no asymptotic assumption hidden. -/
theorem word_universe_bound (N c w x : ℕ) (hN : 2 ≤ N)
    (hw : w ≤ c * Nat.clog 2 N) (hx : x < 2 ^ w) : x < N ^ (2 * c) := by
  apply lt_of_lt_of_le hx
  calc
    2 ^ w ≤ 2 ^ (c * Nat.clog 2 N) := Nat.pow_le_pow_right (by decide) hw
    _ = (2 ^ Nat.clog 2 N) ^ c := by rw [← pow_mul, Nat.mul_comm c]
    _ ≤ (N ^ 2) ^ c := Nat.pow_le_pow_left (ceiling_power_le_square N hN) c
    _ = N ^ (2 * c) := (pow_mul N 2 c).symm

/-- Explicit O(N) transfer theorem for logarithmic-width keys. Physical
layout and the small-memory controller simulation are separate interfaces. -/
theorem logarithmic_word_sort (c w : ℕ) (xs : List ℕ) (hN : 2 ≤ xs.length)
    (hw : w ≤ c * Nat.clog 2 xs.length) (hkeys : ∀ x ∈ xs, x < 2 ^ w) :
    ∃ output,
      radixMachine xs.length (by omega) (2 * c) xs = some (output, 18 * c * xs.length) ∧
      output.Perm xs ∧ output.Pairwise (· ≤ ·) := by
  have hbound : ∀ x ∈ xs, x < xs.length ^ (2 * c) := fun x hx =>
    word_universe_bound xs.length c w x hN hw (hkeys x hx)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    polynomial_universe_sort (2 * c) xs (by omega) hbound

/-- Inputs of length at most one are already sorted and require no movement. -/
def directSort (c : ℕ) (xs : List ℕ) : Option (List ℕ × ℕ) :=
  if h : 2 ≤ xs.length then radixMachine xs.length (by omega) (2 * c) xs
  else some (xs, 0)

theorem directSort_correct (c w : ℕ) (xs : List ℕ)
    (hw : w ≤ c * Nat.clog 2 xs.length) (hkeys : ∀ x ∈ xs, x < 2 ^ w) :
    ∃ output cost, directSort c xs = some (output, cost) ∧
      output.Perm xs ∧ output.Pairwise (· ≤ ·) ∧ cost ≤ 18 * c * xs.length := by
  by_cases hN : 2 ≤ xs.length
  · obtain ⟨output, he, hp, hs⟩ := logarithmic_word_sort c w xs hN hw hkeys
    refine ⟨output, 18 * c * xs.length, ?_, hp, hs, le_rfl⟩
    simpa [directSort, hN] using he
  · refine ⟨xs, 0, by simp [directSort, hN], List.Perm.refl xs, ?_, Nat.zero_le _⟩
    cases xs with
    | nil => simp
    | cons x rest =>
      cases rest with
      | nil => simp
      | cons y tail => simp at hN

/-- Null uses the otherwise unused value N; every non-null pointer is an
original input position. Thus each pointer occupies one finite word. -/
def encodePointer : Pointer n → Fin (n + 1)
  | none => ⟨n, by omega⟩
  | some i => ⟨i.val, by omega⟩

theorem encodePointer_injective : Function.Injective (encodePointer (n := n)) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j => have hj := j.isLt; have he := congrArg Fin.val h; simp [encodePointer] at he; omega
  | some i =>
    cases b with
    | none => have hi := i.isLt; have he := congrArg Fin.val h; simp [encodePointer] at he; omega
    | some j =>
      congr 1
      apply Fin.ext
      exact congrArg (fun p : Fin (n + 1) => p.val) h

/-- Four disjoint disk banks: read-only input, next pointers, output, heads.
All cells are individually addressable dedicated physical blocks. -/
abbrev Address (n K : ℕ) := Sum (Fin n) (Sum (Fin n) (Sum (Fin n) (Fin K)))

theorem disk_blocks : Fintype.card (Address n K) = 3 * n + K := by simp [Address]; omega

/-- Wasting the suffix of each dedicated block still uses quadratic space
when B≤N and K≤N. This counts physical words, including unused padding. -/
theorem disk_space_polynomial (B : ℕ) (hK : K ≤ n) (hB : B ≤ n) :
    Fintype.card (Address n K) * B ≤ 4 * n ^ 2 := by
  rw [disk_blocks]
  calc
    (3 * n + K) * B ≤ (4 * n) * n := Nat.mul_le_mul (by omega) hB
    _ = 4 * n ^ 2 := by ring

/-- Five bounded control words hold cursors, the bucket number, the round number, and the program position. The natural-number execution length is used in the termination statement; the stored control data are the five words listed here. 


-/
structure Control (n K rounds : ℕ) where
  inputCursor : Fin (n + 1)
  outputCursor : Fin (n + 1)
  bucketCursor : Fin (K + 1)
  roundCursor : Fin (rounds + 1)
  pc : Fin 16

/-- The seven resident words comprise one record, one pointer and the five
control words above. The physical transfer buffer is counted separately. -/
def residentWords (B : ℕ) : ℕ := B + 7

theorem resident_memory_fit (M B : ℕ) (h : B + 7 ≤ M) : residentWords B ≤ M := h

theorem resident_memory_fit_large_block (M B : ℕ) (hM : 2 * B ≤ M) (hB : 7 ≤ B) :
    residentWords B ≤ M := by dsimp [residentWords]; omega

/-- Every scalar logical read or write can be compiled to one physical
transfer in the dedicated-block representation. The caller must still
supply the concrete finite-word controller policy. -/
theorem scalar_read_transfer (L D : ℕ) (Word : Type*) (addr : Fin D)
    (win : Normalization.Window L 1) :
    Normalization.primitiveListCost (Normalization.compileCommand
      (.read addr win : Normalization.Command L 1 D Word)) = 1 := by
  exact Normalization.compiled_cost_eq _

theorem scalar_write_transfer (L D : ℕ) (Word : Type*) (addr : Fin D)
    (win : Normalization.Window L 1) :
    Normalization.primitiveListCost (Normalization.compileCommand
      (.write addr win : Normalization.Command L 1 D Word)) = 1 := by
  exact Normalization.compiled_cost_eq _

end CSL.DirectRadix


