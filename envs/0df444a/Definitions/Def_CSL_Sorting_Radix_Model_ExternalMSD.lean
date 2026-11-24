-- Prove2me | Definitions.Def_CSL_Sorting_Radix_Model_ExternalMSD
-- name    : CSL_Sorting_Radix_Model_ExternalMSD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:10:52.882633+00:00
-- url     : https://prove2.me/theorems/ffe68805-b79a-4a7b-9bb8-a977e6466061
-- title:
--   Coded sorting library: Sorting / Radix / Model / ExternalMSD
-- statement:
--   Module `CodedSorting.Sorting.Radix.Model.ExternalMSD` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Concrete high-digit radix recursion. The local sorter is an explicit
--   interface, with an executable Mathlib mergeSort instance. Its I/O contract
--   is separate from mathematical sorting correctness.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Radix.Model.ExternalMSD

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_BucketMachine
import Mathlib.Data.List.Sort
import Definitions.Def_CSL_Interchange_Framework_Recursion_ArbitrarySchedule

section MSD
/-! Concrete high-digit radix recursion. The local sorter is an explicit
interface, with an executable Mathlib mergeSort instance. Its I/O contract
is separate from mathematical sorting correctness. -/

namespace CSL.MSD

open BucketMachine

def digit (base : ℕ) (hb : 0 < base) (remaining x : ℕ) : Fin base :=
  ⟨x / base ^ remaining % base, Nat.mod_lt _ hb⟩

abbrev LocalSorter := (ℕ → ℕ) → List ℕ → List ℕ

def LocalCorrect (localSort : LocalSorter) : Prop :=
  ∀ key xs, (localSort key xs).Perm xs ∧
    (localSort key xs).Pairwise (fun x y => key x ≤ key y)

/-- Actual MSD recursion, with a size cutoff for invoking a local sorter.
All original integer values remain in the records throughout. -/
def sort (base : ℕ) (hb : 0 < base) (threshold : ℕ) (localSort : LocalSorter) :
    ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | fuel + 1, xs =>
      if xs.length ≤ threshold then localSort (fun x => x % base ^ (fuel + 1)) xs
      else (List.finRange base).flatMap fun k =>
        sort base hb threshold localSort fuel (bucket (digit base hb fuel) xs k)

private theorem flatMap_perm {α β : Type*} (keys : List β) (f g : β → List α)
    (h : ∀ k ∈ keys, (f k).Perm (g k)) : (keys.flatMap f).Perm (keys.flatMap g) := by
  induction keys with
  | nil => simp
  | cons k rest ih =>
    simp only [List.flatMap_cons]
    exact (h k (by simp)).append (ih (fun k hk => h k (by simp [hk])))

theorem sort_perm (base : ℕ) (hb : 0 < base) (threshold : ℕ)
    (localSort : LocalSorter) (hc : LocalCorrect localSort) (fuel : ℕ) (xs : List ℕ) :
    (sort base hb threshold localSort fuel xs).Perm xs := by
  induction fuel generalizing xs with
  | zero => exact List.Perm.refl xs
  | succ fuel ih =>
    rw [sort]
    split
    · exact (hc _ xs).1
    · exact (flatMap_perm _ _ _ (fun k _ => ih _)).trans
        (collect_perm (digit base hb fuel) xs)

theorem same_digit_order (base : ℕ) (hb : 0 < base) (fuel x y : ℕ)
    (hd : digit base hb fuel x = digit base hb fuel y)
    (hr : x % base ^ fuel ≤ y % base ^ fuel) :
    x % base ^ (fuel + 1) ≤ y % base ^ (fuel + 1) := by
  have hd' : x / base ^ fuel % base = y / base ^ fuel % base := congrArg Fin.val hd
  simp only [Nat.mod_pow_succ]
  rw [hd']
  omega

theorem different_digit_order (base : ℕ) (hb : 0 < base) (fuel x y : ℕ)
    (hd : digit base hb fuel x < digit base hb fuel y) :
    x % base ^ (fuel + 1) ≤ y % base ^ (fuel + 1) := by
  have hd' : x / base ^ fuel % base < y / base ^ fuel % base := hd
  have hp : 0 < base ^ fuel := Nat.pow_pos hb
  have hx := Nat.mod_lt x hp
  have hy : 0 ≤ y % base ^ fuel := Nat.zero_le _
  simp only [Nat.mod_pow_succ]
  have hm := Nat.mul_le_mul_left (base ^ fuel) (Nat.succ_le_of_lt hd')
  simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hm
  omega

/-- Inductive invariant: the result is sorted by the unprocessed low digits.
No assumption that the original keys were already bounded is needed here. -/
theorem sort_pairwise_remainder (base : ℕ) (hb : 0 < base) (threshold : ℕ)
    (localSort : LocalSorter) (hc : LocalCorrect localSort) (fuel : ℕ) (xs : List ℕ) :
    (sort base hb threshold localSort fuel xs).Pairwise
      (fun x y => x % base ^ fuel ≤ y % base ^ fuel) := by
  induction fuel generalizing xs with
  | zero =>
    simp only [sort, pow_zero, Nat.mod_one]
    exact List.pairwise_of_forall (by intro a b; exact Nat.le_refl 0)
  | succ fuel ih =>
    rw [sort]
    split
    · exact (hc _ xs).2
    · let child := fun k => sort base hb threshold localSort fuel
          (bucket (digit base hb fuel) xs k)
      have hmem (k : Fin base) (x : ℕ) (hx : x ∈ child k) : digit base hb fuel x = k := by
        have hp := sort_perm base hb threshold localSort hc fuel
          (bucket (digit base hb fuel) xs k)
        exact (mem_bucket _ _ _ _).mp (hp.mem_iff.mp hx) |>.2
      change ((List.finRange base).map child).flatten.Pairwise _
      apply BucketOrder.pairwise_flatten_of_buckets
      · intro ys hys
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hys
        apply (ih (bucket (digit base hb fuel) xs k)).imp_of_mem
        intro x y hx hy hxy
        exact same_digit_order base hb fuel x y ((hmem k x hx).trans (hmem k y hy).symm) hxy
      · apply (List.pairwise_lt_finRange base).map child
        intro k l hkl
        intro x hx y hy
        apply different_digit_order base hb fuel x y
        rw [hmem k x hx, hmem l y hy]
        exact hkl

/-- Complete mathematical sorting correctness for bounded integer keys. -/
theorem sort_correct (base : ℕ) (hb : 0 < base) (threshold : ℕ)
    (localSort : LocalSorter) (hc : LocalCorrect localSort) (fuel : ℕ) (xs : List ℕ)
    (hbound : ∀ x ∈ xs, x < base ^ fuel) :
    (sort base hb threshold localSort fuel xs).Perm xs ∧
      (sort base hb threshold localSort fuel xs).Pairwise (· ≤ ·) := by
  have hp := sort_perm base hb threshold localSort hc fuel xs
  refine ⟨hp, ?_⟩
  apply (sort_pairwise_remainder base hb threshold localSort hc fuel xs).imp_of_mem
  intro x y hx hy hxy
  simpa only [Nat.mod_eq_of_lt (hbound x (hp.mem_iff.mp hx)),
    Nat.mod_eq_of_lt (hbound y (hp.mem_iff.mp hy))] using hxy

/-- A concrete instance, reusing the standard library's merge-sort proof. -/
def mergeLocal : LocalSorter := fun key xs => xs.mergeSort (fun x y => key x ≤ key y)

theorem mergeLocal_correct : LocalCorrect mergeLocal := by
  intro key xs
  constructor
  · exact List.mergeSort_perm xs _
  · simpa [mergeLocal] using List.sorted_mergeSort (le := fun x y => decide (key x ≤ key y))
      (by intro a b c hab hbc; simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (by intro a b; simpa using le_total (key a) (key b)) xs

/-- The number of block transfers charged to the actual buffered partition
and stream reconstruction. No scan bound is an input to this definition. -/
def partitionCost (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (fuel : ℕ) (xs : List ℕ) : ℕ :=
  distributionTransfers (digit base hb fuel) B hB xs +
    reconstructionTransfers (digit base hb fuel) B hB xs

abbrev LocalCost := (ℕ → ℕ) → List ℕ → ℕ

/-- Compositional cost of this recursion. The local routine is charged through
its explicit interface; replacing it by the paper's local routine still
requires a proved implementation/cost contract. -/
def cost (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (threshold : ℕ) (localCost : LocalCost) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, xs =>
      if xs.length ≤ threshold then localCost (fun x => x % base ^ (fuel + 1)) xs
      else partitionCost base hb B hB fuel xs +
        ((List.finRange base).map fun k =>
          cost base hb B hB threshold localCost fuel
            (bucket (digit base hb fuel) xs k)).sum

/-- Exact bounded-overhead statement for each nonterminal bucket operation. -/
theorem partitionCost_bound (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (fuel : ℕ) (xs : List ℕ) :
    partitionCost base hb B hB fuel xs ≤ 4 * (xs.length / B) + 2 * base + 2 :=
  complete_bucket_transfer_bound (digit base hb fuel) B hB xs

theorem partitionCost_linear (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (threshold fuel : ℕ) (xs : List ℕ)
    (ht : base ≤ threshold) (hn : threshold < xs.length) :
    partitionCost base hb B hB fuel xs ≤ 8 * xs.length := by
  have h := partitionCost_bound base hb B hB fuel xs
  have hdiv := Nat.div_le_self xs.length B
  omega

private theorem sum_pointwise_bound {α : Type*} (keys : List α)
    (f size : α → ℕ) (C : ℕ) (h : ∀ k ∈ keys, f k ≤ C * size k) :
    (keys.map f).sum ≤ C * (keys.map size).sum := by
  induction keys with
  | nil => simp
  | cons k rest ih =>
    have hk := h k (by simp)
    have hr := ih (fun k hk => h k (by simp [hk]))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- Complete finite induction for the concrete MSD control structure. The
partition cost is derived, not assumed. Only the local routine's cost is
supplied. This coarse bound is NOT the paper's accelerated I/O bound. -/
theorem cost_linear_depth (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (threshold : ℕ) (ht : base ≤ threshold) (localCost : LocalCost) (L : ℕ)
    (hlocal : ∀ key xs, localCost key xs ≤ L * xs.length)
    (fuel : ℕ) (xs : List ℕ) :
    cost base hb B hB threshold localCost fuel xs ≤ (8 * fuel + L) * xs.length := by
  induction fuel generalizing xs with
  | zero => simp [cost]
  | succ fuel ih =>
    rw [cost]
    split
    · calc
        localCost _ xs ≤ L * xs.length := hlocal _ xs
        _ ≤ (8 * (fuel + 1) + L) * xs.length := Nat.mul_le_mul_right _ (by omega)
    · rename_i hlarge
      have hp := partitionCost_linear base hb B hB threshold fuel xs ht (by omega)
      have hc := sum_pointwise_bound (List.finRange base)
        (fun k => cost base hb B hB threshold localCost fuel
          (bucket (digit base hb fuel) xs k))
        (fun k => (bucket (digit base hb fuel) xs k).length)
        (8 * fuel + L) (fun k _ => ih _)
      rw [total_bucket_lengths] at hc
      nlinarith

end CSL.MSD
end MSD

section ExternalMSD
/-! Section 7.1: sort chunks locally, then materialize each contiguous
same-key interval as an aligned scratch stream. This extra sequential pass
is an implementation variant with the same asymptotic boundary overhead.
Only one input and one output block buffer are needed during materialization
or gathering; no simultaneous K output buffers are used here. -/

namespace CSL.ExternalMSD

open BucketMachine

variable {α : Type*} {K : ℕ}

def interval (key : α → Fin K) (xs : List α) (k : Fin K) : List α :=
  (xs.dropWhile (fun a => key a < k)).takeWhile (fun a => key a == k)

/-- The interval representation is genuinely contiguous. -/
theorem interval_contiguous (key : α → Fin K) (xs : List α) (k : Fin K) :
    ∃ before after, xs = before ++ interval key xs k ++ after := by
  refine ⟨xs.takeWhile (fun a => key a < k),
    (xs.dropWhile (fun a => key a < k)).dropWhile (fun a => key a == k), ?_⟩
  unfold interval
  rw [List.append_assoc, List.takeWhile_append_dropWhile, List.takeWhile_append_dropWhile]

theorem sorted_interval_is_bucket (key : α → Fin K) (xs : List α)
    (hs : xs.Pairwise (fun a b => key a ≤ key b)) (k : Fin K) :
    interval key xs k = bucket key xs k := by
  induction xs with
  | nil => simp [interval, bucket]
  | cons a rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    by_cases hlt : key a < k
    · have hne : key a ≠ k := ne_of_lt hlt
      simpa [interval, bucket, hlt, hne] using ih htail
    · by_cases heq : key a = k
      · have hdrop : rest.dropWhile (fun a => key a < k) = rest := by
          cases rest with
          | nil => rfl
          | cons b tail =>
            have hle := hhead b (by simp)
            have hn : ¬ key b < k := by rw [heq] at hle; exact not_lt_of_ge hle
            simp [hn]
        have hi := ih htail
        unfold interval at hi
        rw [hdrop] at hi
        simp only [interval, List.dropWhile_cons, hlt, decide_false, Bool.false_eq_true,
          ↓reduceIte, List.takeWhile_cons, heq, beq_self_eq_true, ↓reduceIte,
          bucket, List.filter_cons]
        simpa [bucket, heq] using congrArg (List.cons a) hi
      · have hg : k < key a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
        have hempty : bucket key (a :: rest) k = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          have hge : key a ≤ key b := by
            rcases List.mem_cons.mp hb with rfl | hb
            · exact le_rfl
            · exact hhead b hb
          have hn : key b ≠ k := ne_of_gt (lt_of_lt_of_le hg hge)
          simpa using hn
        rw [hempty]
        simp [interval, hlt, heq]

def sortedChunks (chunk : ℕ) (hc : 0 < chunk) (localSort : List α → List α)
    (xs : List α) : List (List α) := (pack chunk hc xs).map localSort

def fragments (key : α → Fin K) (rows : List (List α)) : List (List α) :=
  rows.flatMap fun row => (List.finRange K).map (bucket key row)

def gather (key : α → Fin K) (rows : List (List α)) : List α :=
  (List.finRange K).flatMap fun k => rows.flatMap (fun row => bucket key row k)

private theorem bucket_flatten (key : α → Fin K) (rows : List (List α)) (k : Fin K) :
    bucket key rows.flatten k = rows.flatMap (fun row => bucket key row k) := by
  induction rows with
  | nil => simp [bucket]
  | cons row rest ih =>
    change bucket key (row ++ rest.flatten) k = bucket key row k ++ rest.flatMap (fun row => bucket key row k)
    simpa only [bucket, List.filter_append] using congrArg (fun t => bucket key row k ++ t) ih

theorem gather_eq_collect (key : α → Fin K) (rows : List (List α)) :
    gather key rows = collect key rows.flatten := by
  unfold gather collect
  apply congrArg (List.flatMap · (List.finRange K))
  funext k
  exact (bucket_flatten key rows k).symm

theorem gather_perm (key : α → Fin K) (rows : List (List α)) :
    (gather key rows).Perm rows.flatten := by
  rw [gather_eq_collect]
  exact collect_perm key rows.flatten

theorem sortedChunks_perm (chunk : ℕ) (hc : 0 < chunk) (localSort : List α → List α)
    (hp : ∀ row, (localSort row).Perm row) (xs : List α) :
    (sortedChunks chunk hc localSort xs).flatten.Perm xs := by
  have h : ∀ rows : List (List α), (rows.map localSort).flatten.Perm rows.flatten := by
    intro rows
    induction rows with
    | nil => simp
    | cons row rest ih => simpa using (hp row).append ih
  simpa [sortedChunks, flatten_pack] using h (pack chunk hc xs)

theorem partition_perm (key : α → Fin K) (chunk : ℕ) (hc : 0 < chunk)
    (localSort : List α → List α) (hp : ∀ row, (localSort row).Perm row) (xs : List α) :
    (gather key (sortedChunks chunk hc localSort xs)).Perm xs :=
  (gather_perm key _).trans (sortedChunks_perm chunk hc localSort hp xs)

theorem fragment_count (key : α → Fin K) (rows : List (List α)) :
    (fragments key rows).length = rows.length * K := by
  simp [fragments, List.length_flatMap, Function.comp_def, List.map_const']

theorem fragment_volume (key : α → Fin K) (rows : List (List α)) :
    (fragments key rows).flatten.length = rows.flatten.length := by
  induction rows with
  | nil => simp [fragments]
  | cons row rest ih =>
    simp only [fragments, List.flatMap_cons, List.flatten_append, List.length_append,
      List.flatten_cons]
    have hrow : ((List.finRange K).map (bucket key row)).flatten.length = row.length :=
      collect_length key row
    rw [hrow]
    simpa only [fragments] using congrArg (fun n => row.length + n) ih

/-- These are actual stored blocks for each interval, independently aligned.
The intervals are processed one at a time in row/key order. -/
def storedFragments (key : α → Fin K) (B : ℕ) (hB : 0 < B) (rows : List (List α)) :=
  (fragments key rows).map (pack B hB)

theorem storedFragments_contents (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (rows : List (List α)) :
    (storedFragments key B hB rows).map List.flatten = fragments key rows := by
  simp [storedFragments, List.map_map, Function.comp_def, flatten_pack]

def transferSum (B : ℕ) (hB : 0 < B) (streams : List (List α)) : ℕ :=
  (streams.map fun row => (pack B hB row).length).sum

theorem transferSum_capacity (B : ℕ) (hB : 0 < B) (streams : List (List α)) :
    transferSum B hB streams * B ≤ streams.flatten.length + streams.length * B := by
  induction streams with
  | nil => simp [transferSum]
  | cons row rest ih =>
    have hr := Nat.le_of_lt (pack_capacity B hB row).2
    simp only [transferSum, List.map_cons, List.sum_cons, Nat.add_mul,
      List.flatten_cons, List.length_append, List.length_cons, Nat.one_mul] at ih ⊢
    omega

theorem fragment_transfer_capacity (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (rows : List (List α)) :
    transferSum B hB (fragments key rows) * B ≤ rows.flatten.length + rows.length * K * B := by
  simpa only [fragment_volume, fragment_count] using
    transferSum_capacity B hB (fragments key rows)

/-- The local routine's only correctness contract is permutation plus
ordering by this digit. Hence the extracted fragments really are intervals. -/
theorem local_fragments_contiguous (key : α → Fin K)
    (chunk : ℕ) (hc : 0 < chunk) (localSort : List α → List α)
    (hs : ∀ row, (localSort row).Pairwise (fun a b => key a ≤ key b))
    (xs : List α) (row : List α) (hr : row ∈ sortedChunks chunk hc localSort xs)
    (k : Fin K) : ∃ before after, row = before ++ bucket key row k ++ after := by
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp hr
  rw [← sorted_interval_is_bucket key _ (hs source)]
  exact interval_contiguous key _ k

theorem gather_pairwise (key : α → Fin K) (rows : List (List α)) :
    (gather key rows).Pairwise (fun x y => key x ≤ key y) := by
  rw [gather_eq_collect]
  change ((List.finRange K).map (bucket key rows.flatten)).flatten.Pairwise _
  apply BucketOrder.pairwise_flatten_of_buckets
  · intro ys hys
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hys
    have ht : (bucket key rows.flatten k).Pairwise (fun _ _ => True) :=
      List.pairwise_of_forall (by intros; trivial)
    apply ht.imp_of_mem
    intro x y hx hy _
    rw [(mem_bucket key _ _ _).mp hx |>.2, (mem_bucket key _ _ _).mp hy |>.2]
  · apply (List.pairwise_lt_finRange K).map (bucket key rows.flatten)
    intro k l hkl x hx y hy
    rw [(mem_bucket key _ _ _).mp hx |>.2, (mem_bucket key _ _ _).mp hy |>.2]
    exact le_of_lt hkl

/-- In an already digit-sorted chunk, enumerating all digit intervals
reproduces the chunk verbatim. This justifies one sequential input scan. -/
theorem collect_sorted (key : α → Fin K) (xs : List α)
    (hs : xs.Pairwise (fun x y => key x ≤ key y)) : collect key xs = xs := by
  induction xs with
  | nil => simp [collect, bucket]
  | cons a rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    obtain ⟨left, right, he⟩ := List.mem_iff_append.mp (List.mem_finRange (key a))
    have hkeys := List.pairwise_lt_finRange K
    rw [he] at hkeys
    obtain ⟨_, hright, hcross⟩ := List.pairwise_append.mp hkeys
    have hl (k : Fin K) (hk : k ∈ left) : k < key a := hcross k hk (key a) (by simp)
    have hr (k : Fin K) (hk : k ∈ right) : key a < k := (List.pairwise_cons.mp hright).1 k hk
    have hempty (k : Fin K) (hk : k ∈ left) : bucket key rest k = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hg := hhead x hx
      have hlt := hl k hk
      have hn : key x ≠ k := ne_of_gt (lt_of_lt_of_le hlt hg)
      simpa using hn
    have hleft : left.flatMap (bucket key rest) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      exact hempty
    have hleft' : left.flatMap (bucket key (a :: rest)) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro k hk
      simp [bucket, ne_of_gt (hl k hk), show rest.filter (fun x => key x == k) = [] from hempty k hk]
    have hright' : right.flatMap (bucket key (a :: rest)) = right.flatMap (bucket key rest) := by
      apply List.flatMap_congr
      intro k hk
      simp [bucket, ne_of_lt (hr k hk)]
    have hi := ih htail
    unfold collect at hi ⊢
    rw [he, List.flatMap_append, hleft, List.nil_append, List.flatMap_cons] at hi
    rw [he, List.flatMap_append, hleft', List.nil_append, List.flatMap_cons, hright']
    simpa [bucket] using congrArg (List.cons a) hi

/-- Read sorted rows once; write each interval separately, then read these
interval files once in key/row order and write a packed output. Each of the
J K descriptors is conservatively charged one block write and one read. -/
def gatheringTransfers (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (rows : List (List α)) : ℕ :=
  transferSum B hB rows + 2 * transferSum B hB (fragments key rows) +
    (pack B hB (gather key rows)).length + 2 * rows.length * K

theorem gathering_capacity (key : α → Fin K) (B : ℕ) (hB : 0 < B)
    (rows : List (List α)) :
    gatheringTransfers key B hB rows * B ≤
      4 * rows.flatten.length + rows.length * B + 4 * rows.length * K * B + B := by
  have hr := transferSum_capacity B hB rows
  have hf := fragment_transfer_capacity key B hB rows
  have ho := Nat.le_of_lt (pack_capacity B hB (gather key rows)).2
  rw [(gather_perm key rows).length_eq] at ho
  unfold gatheringTransfers
  nlinarith

theorem sortedChunks_length (chunk : ℕ) (hc : 0 < chunk)
    (localSort : List α → List α) (xs : List α) :
    (sortedChunks chunk hc localSort xs).length = Recurrence.chunkCount xs.length chunk := by
  simp [sortedChunks, pack_count, Recurrence.chunkCount]

/-- Boundary overhead is absorbed using exactly the paper's H² chunk size,
B ≤ H, and K ≤ H. This bound has no K-block memory requirement. -/
theorem gathering_scan_bound (key : α → Fin K) (B H : ℕ)
    (hB : 0 < B) (hH : 0 < H) (hBH : B ≤ H) (hK : K ≤ H) (hKpos : 0 < K)
    (localSort : List α → List α) (hp : ∀ row, (localSort row).Perm row)
    (xs : List α) (hn : H ^ 2 ≤ xs.length) :
    gatheringTransfers key B hB (sortedChunks (H ^ 2) (Nat.pow_pos hH) localSort xs) * B ≤
      14 * xs.length + B := by
  let rows := sortedChunks (H ^ 2) (Nat.pow_pos hH) localSort xs
  have hv : rows.flatten.length = xs.length :=
    (sortedChunks_perm _ _ localSort hp xs).length_eq
  have hm : rows.length * K * B ≤ 2 * xs.length := by
    rw [show rows.length = Recurrence.chunkCount xs.length (H ^ 2) from
      sortedChunks_length _ _ localSort xs]
    exact Recurrence.bucket_metadata_bound _ H B K hn hBH hK
  have hr : rows.length * B ≤ rows.length * K * B := by
    exact Nat.mul_le_mul_right B (by nlinarith)
  have hg := gathering_capacity key B hB rows
  rw [hv] at hg
  nlinarith

theorem gathering_scan_count (key : α → Fin K) (B H : ℕ)
    (hB : 0 < B) (hH : 0 < H) (hBH : B ≤ H) (hK : K ≤ H) (hKpos : 0 < K)
    (localSort : List α → List α) (hp : ∀ row, (localSort row).Perm row)
    (xs : List α) (hn : H ^ 2 ≤ xs.length) :
    gatheringTransfers key B hB (sortedChunks (H ^ 2) (Nat.pow_pos hH) localSort xs) ≤
      14 * xs.length / B + 1 := by
  have h := gathering_scan_bound key B H hB hH hBH hK hKpos localSort hp xs hn
  have hd := (Nat.le_div_iff_mul_le hB).mpr h
  simpa [Nat.add_div_right _ hB] using hd

/-- The same interval of key k, concatenated in the original chunk order. -/
def child (key : α → Fin K) (rows : List (List α)) (k : Fin K) : List α :=
  rows.flatMap (fun row => bucket key row k)

theorem child_key (key : α → Fin K) (rows : List (List α)) (k : Fin K)
    (x : α) (hx : x ∈ child key rows k) : key x = k := by
  obtain ⟨row, _, hx⟩ := List.mem_flatMap.mp hx
  exact (mem_bucket key row k x).mp hx |>.2

theorem children_volume (key : α → Fin K) (rows : List (List α)) :
    ((List.finRange K).map (fun k => (child key rows k).length)).sum = rows.flatten.length := by
  have h := (gather_perm key rows).length_eq
  simpa [gather, child, List.length_flatMap, Function.comp_def] using h

private theorem flatMap_perm {β : Type*} (keys : List β) (f g : β → List α)
    (h : ∀ k ∈ keys, (f k).Perm (g k)) : (keys.flatMap f).Perm (keys.flatMap g) := by
  induction keys with
  | nil => simp
  | cons k rest ih =>
    simp only [List.flatMap_cons]
    exact (h k (by simp)).append (ih (fun k hk => h k (by simp [hk])))

def prepare (base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H)
    (localSort : MSD.LocalSorter) (fuel : ℕ) (xs : List ℕ) : List (List ℕ) :=
  sortedChunks (H ^ 2) (Nat.pow_pos hH)
    (localSort (fun x => (MSD.digit base hb fuel x).val)) xs

/-- The actual Section 7.1 control structure: local chunk sorting precedes
interval gathering; only then are the gathered digit classes recursed on. -/
def sort (base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H)
    (localSort : MSD.LocalSorter) : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | fuel + 1, xs =>
      if xs.length ≤ H ^ 2 then localSort (fun x => x % base ^ (fuel + 1)) xs
      else (List.finRange base).flatMap fun k =>
        sort base hb H hH localSort fuel
          (child (MSD.digit base hb fuel) (prepare base hb H hH localSort fuel xs) k)

theorem prepare_perm (base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H)
    (localSort : MSD.LocalSorter) (hc : MSD.LocalCorrect localSort) (fuel : ℕ) (xs : List ℕ) :
    (prepare base hb H hH localSort fuel xs).flatten.Perm xs :=
  sortedChunks_perm _ _ _ (fun row => (hc _ row).1) xs

theorem sort_perm (base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H)
    (localSort : MSD.LocalSorter) (hc : MSD.LocalCorrect localSort) (fuel : ℕ) (xs : List ℕ) :
    (sort base hb H hH localSort fuel xs).Perm xs := by
  induction fuel generalizing xs with
  | zero => exact List.Perm.refl xs
  | succ fuel ih =>
    rw [sort]
    split
    · exact (hc _ xs).1
    · exact (flatMap_perm _ _ _ (fun k _ => ih _)).trans
        ((gather_perm (MSD.digit base hb fuel) _).trans
          (prepare_perm base hb H hH localSort hc fuel xs))

theorem sort_pairwise_remainder (base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H)
    (localSort : MSD.LocalSorter) (hc : MSD.LocalCorrect localSort) (fuel : ℕ) (xs : List ℕ) :
    (sort base hb H hH localSort fuel xs).Pairwise
      (fun x y => x % base ^ fuel ≤ y % base ^ fuel) := by
  induction fuel generalizing xs with
  | zero =>
    simp only [sort, pow_zero, Nat.mod_one]
    exact List.pairwise_of_forall (by intro a b; exact Nat.le_refl 0)
  | succ fuel ih =>
    rw [sort]
    split
    · exact (hc _ xs).2
    · let rows := prepare base hb H hH localSort fuel xs
      let output := fun k => sort base hb H hH localSort fuel
          (child (MSD.digit base hb fuel) rows k)
      have hm (k : Fin base) (x : ℕ) (hx : x ∈ output k) : MSD.digit base hb fuel x = k := by
        exact child_key _ _ _ x ((sort_perm base hb H hH localSort hc fuel _).mem_iff.mp hx)
      change ((List.finRange base).map output).flatten.Pairwise _
      apply BucketOrder.pairwise_flatten_of_buckets
      · intro ys hys
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hys
        apply (ih (child (MSD.digit base hb fuel) rows k)).imp_of_mem
        intro x y hx hy hxy
        exact MSD.same_digit_order base hb fuel x y ((hm k x hx).trans (hm k y hy).symm) hxy
      · apply (List.pairwise_lt_finRange base).map output
        intro k l hkl x hx y hy
        apply MSD.different_digit_order base hb fuel x y
        rw [hm k x hx, hm l y hy]
        exact hkl

/-- End-to-end sorting semantics for the chunk/interval implementation.
The local-sort correctness contract can be discharged by Mathlib mergeSort
or by any later verified implementation of the paper's local routine. -/
theorem sort_correct (base : ℕ) (hb : 0 < base) (H : ℕ) (hH : 0 < H)
    (localSort : MSD.LocalSorter) (hc : MSD.LocalCorrect localSort) (fuel : ℕ) (xs : List ℕ)
    (hbound : ∀ x ∈ xs, x < base ^ fuel) :
    (sort base hb H hH localSort fuel xs).Perm xs ∧
      (sort base hb H hH localSort fuel xs).Pairwise (· ≤ ·) := by
  have hp := sort_perm base hb H hH localSort hc fuel xs
  refine ⟨hp, ?_⟩
  apply (sort_pairwise_remainder base hb H hH localSort hc fuel xs).imp_of_mem
  intro x y hx hy hxy
  simpa only [Nat.mod_eq_of_lt (hbound x (hp.mem_iff.mp hx)),
    Nat.mod_eq_of_lt (hbound y (hp.mem_iff.mp hy))] using hxy

def chunkSortingCost (H : ℕ) (hH : 0 < H) (localCost : MSD.LocalCost)
    (key : ℕ → ℕ) (xs : List ℕ) : ℕ :=
  ((pack (H ^ 2) (Nat.pow_pos hH) xs).map (localCost key)).sum

/-- The count is defined from actual block packs and interval files; only
the cost of the supplied local routine is an explicit external parameter. -/
def cost (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (H : ℕ) (hH : 0 < H) (localSort : MSD.LocalSorter) (localCost : MSD.LocalCost) :
    ℕ → List ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, xs =>
      if xs.length ≤ H ^ 2 then localCost (fun x => x % base ^ (fuel + 1)) xs
      else chunkSortingCost H hH localCost (fun x => (MSD.digit base hb fuel x).val) xs +
        gatheringTransfers (MSD.digit base hb fuel) B hB (prepare base hb H hH localSort fuel xs) +
        ((List.finRange base).map fun k => cost base hb B hB H hH localSort localCost fuel
          (child (MSD.digit base hb fuel) (prepare base hb H hH localSort fuel xs) k)).sum

private theorem sum_affine_bound {β : Type*} (items : List β) (f size : β → ℕ)
    (B C D : ℕ) (h : ∀ a ∈ items, f a * B ≤ C * size a + D) :
    (items.map f).sum * B ≤ C * (items.map size).sum + D * items.length := by
  induction items with
  | nil => simp
  | cons a rest ih =>
    have ha := h a (by simp)
    have hr := ih (fun a ha => h a (by simp [ha]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem chunkSortingCost_bound (B H L : ℕ) (hH : 0 < H) (hBH : B ≤ H)
    (localCost : MSD.LocalCost)
    (hl : ∀ key xs, xs.length ≤ H ^ 2 → localCost key xs * B ≤ L * (xs.length + B))
    (key : ℕ → ℕ) (xs : List ℕ) (hn : H ^ 2 ≤ xs.length) :
    chunkSortingCost H hH localCost key xs * B ≤ 3 * L * xs.length := by
  have hs := sum_affine_bound (pack (H ^ 2) (Nat.pow_pos hH) xs) (localCost key)
    List.length B L (L * B) (by
      intro row hr
      have hc := block_size_bound _ _ xs row hr
      simpa only [Nat.mul_add] using hl key row hc)
  have hv : ((pack (H ^ 2) (Nat.pow_pos hH) xs).map List.length).sum = xs.length := by
    rw [← List.length_flatten, flatten_pack]
  have hm := Recurrence.bucket_metadata_bound xs.length H B 1 hn hBH (by omega)
  simp only [Nat.mul_one] at hm
  rw [pack_count] at hs
  change chunkSortingCost H hH localCost key xs * B ≤ _ at hs
  rw [hv] at hs
  unfold Recurrence.chunkCount at hm
  nlinarith

/-- Finite-depth I/O composition for the actual H²-chunk construction.
L describes the local routine's per-scan cost; it is not the desired global
bound inserted as an assumption. Additive local startup costs are absorbed
at internal nodes using base·B ≤ H² < n. -/
theorem cost_depth_bound (base : ℕ) (hb : 0 < base) (B : ℕ) (hB : 0 < B)
    (H : ℕ) (hH : 0 < H) (hBH : B ≤ H) (hbase : base ≤ H)
    (localSort : MSD.LocalSorter) (hc : MSD.LocalCorrect localSort)
    (localCost : MSD.LocalCost) (L : ℕ)
    (hl : ∀ key xs, xs.length ≤ H ^ 2 → localCost key xs * B ≤ L * (xs.length + B))
    (fuel : ℕ) (xs : List ℕ) :
    cost base hb B hB H hH localSort localCost fuel xs * B ≤
      ((4 * L + 15) * fuel + L) * xs.length + L * B := by
  induction fuel generalizing xs with
  | zero => simp [cost]
  | succ fuel ih =>
    rw [cost]
    split
    · rename_i hsmall
      have h := hl (fun x => x % base ^ (fuel + 1)) xs hsmall
      have hm := Nat.mul_le_mul_right xs.length
        (show L ≤ (4 * L + 15) * (fuel + 1) + L by omega)
      rw [Nat.mul_add] at h
      omega
    · rename_i hlarge
      have hn : H ^ 2 ≤ xs.length := by omega
      have hKB : base * B ≤ H ^ 2 := by
        calc
          base * B ≤ H * H := Nat.mul_le_mul hbase hBH
          _ = H ^ 2 := by ring
      have hBn : B ≤ xs.length := by nlinarith
      have hlocal := chunkSortingCost_bound B H L hH hBH localCost hl
        (fun x => (MSD.digit base hb fuel x).val) xs hn
      have hg := gathering_scan_bound (MSD.digit base hb fuel) B H hB hH hBH hbase hb
        (localSort (fun x => (MSD.digit base hb fuel x).val))
        (fun row => (hc _ row).1) xs hn
      change gatheringTransfers _ B hB (prepare base hb H hH localSort fuel xs) * B ≤ _ at hg
      have hchildren := sum_affine_bound (List.finRange base)
        (fun k => cost base hb B hB H hH localSort localCost fuel
          (child (MSD.digit base hb fuel) (prepare base hb H hH localSort fuel xs) k))
        (fun k => (child (MSD.digit base hb fuel) (prepare base hb H hH localSort fuel xs) k).length)
        B ((4 * L + 15) * fuel + L) (L * B) (fun k _ => ih _)
      rw [children_volume, (prepare_perm base hb H hH localSort hc fuel xs).length_eq,
        List.length_finRange] at hchildren
      have hstart : L * B * base ≤ L * xs.length := by nlinarith
      nlinarith

end CSL.ExternalMSD
end ExternalMSD


