-- Prove2me | Definitions.Def_Bdd_Reduce_Main
-- name    : Bdd_Reduce_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:14:51.757409+00:00
-- url     : https://prove2.me/theorems/37453d75-bbd9-43ca-9f91-2f4e4984eb13
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Main.lean

import Definitions.Def_Bdd_Reduce_Process
import Definitions.Def_Bdd_Reduce_Discover
import Theorems.Thm_Bdd_reduced_of_terminal
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_OBdd_discover_spec
import Theorems.Thm_OBdd_discover_spec_inv
import Theorems.Thm_OBdd_reduced_of_terminal
import Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937
import Theorems.Thm_Reduce_allAbove_initial
import Theorems.Thm_Reduce_heapInjective_initial
import Theorems.Thm_Reduce_inv_initial
import Theorems.Thm_Reduce_keyLE_sentinel
import Theorems.Thm_Reduce_keyLE_sorted_mergeSort
import Theorems.Thm_Reduce_sentinel_no_match
import Theorems.Thm_Reduce_varInvariant_initial
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
open Pointer
open Bdd
open RawBdd
namespace Reduce
def step {n m : Nat} (O : OBdd n m)
    (vlist : Vector (List (Fin m)) n) (i : Fin n)
    (ps : ProvedState n m) (inv : Invariant O ps i.1)
    (hdiscover_inv : ∀ j ∈ vlist[i],
        O.1.heap[j].var.1 = i.1 ∧ Reachable O.1.heap O.1.root (.node j))
    (hvarinv : VarInvariant O ps) (hallabove : AllAbove ps i.1)
    (hheapinj : HeapInjective ps) :
    { ps' : ProvedState n m //
        Invariant O ps' i.1 ∧
        (∀ j ∈ vlist[i], Reachable O.1.heap O.1.root (.node j) → (ps'.state.ids[j]).isSome) ∧
        VarInvariant O ps' ∧
        (0 < i.1 → AllAbove ps' (i.1 - 1)) ∧
        HeapInjective ps' } :=
  -- Build the queue: redundant nodes (lid = hid) are resolved immediately;
  -- non-redundant nodes are collected in `queue` as ((lid, hid), j) entries.
  let ⟨⟨ps₁, queue⟩, inv₁, hsize₁, hpres₁, _, hmono₁, hpost₁, hrest₁⟩ :=
    populate_queue O i [] vlist[i] ps inv
      (fun j hj => (hdiscover_inv j hj).1)
      (fun j hj => (hdiscover_inv j hj).2)
      -- empty accumulator: trivially bounded
      (fun _ h => by simp at h)
      -- empty accumulator: trivially non-redundant
      (fun _ h => by simp at h)
      -- empty accumulator: trivially entry-correct
      (fun _ h => by simp at h)
      hvarinv
  let hbounds₁ := hrest₁.1
  let hnonred₁ := hrest₁.2.1
  let hec₁ := hrest₁.2.2.1
  let hvarinv₁ := hrest₁.2.2.2
  -- Sort the queue so that equal-key entries are adjacent.
  -- Setninel (⟨.inl false, .inl false⟩, .inl false): all real entries have key.1 ≠ key.2
  -- (populate_queue only enqueues non-redundant nodes), so the sentinel never matches
  -- any entry, hence the first element always starts a fresh equivalence class.
  let sorted := queue.mergeSort (fun a b => leKeyPair a.1 b.1)
  -- Process the sorted queue, assigning output pointers to each equivalence class.
  -- Bounds for sorted entries: sorting is a permutation, so bounds transfer from queue.
  have hbounds_sorted : ∀ entry ∈ sorted,
      entry.1.1.Bounded ps₁.state.size ∧ entry.1.2.Bounded ps₁.state.size := by
    intro entry hmem
    have := hbounds₁ entry ((List.Perm.mem_iff (List.mergeSort_perm _ _)).mp hmem)
    exact this
  have hnonred_sorted : ∀ entry ∈ sorted, entry.1.1 ≠ entry.1.2 := by
    intro entry hmem
    exact hnonred₁ entry ((List.Perm.mem_iff (List.mergeSort_perm _ _)).mp hmem)
  have hec_sorted : ∀ entry ∈ sorted, EntryCorrect O ps₁ i.1 entry := by
    intro entry hmem
    exact hec₁ entry ((List.Perm.mem_iff (List.mergeSort_perm _ _)).mp hmem)
  -- The level invariant for the sorted queue: prefix is the whole (pre-push) heap, above
  -- level i; queue is sorted with all keys ≥ the (least) sentinel; suffix/curptr empty.
  have si : StepInv O ps₁ i.1 ps₁.state.size ⟨.inl false, .inl false⟩ (.inl false) sorted :=
    { hs0        := le_refl _
      hbase      := fun k _ => (hpres₁ ⟨hallabove, hheapinj⟩).1 k
      hsuffix    := fun k hk => absurd hk (Nat.not_le.mpr k.isLt)
      hheapinj   := (hpres₁ ⟨hallabove, hheapinj⟩).2
      hvarinv    := hvarinv₁
      hcurlvl    := fun k h => by simp at h
      hnonred    := hnonred_sorted
      hbounds0   := hbounds_sorted
      hsorted    := keyLE_sorted_mergeSort queue
      hcur_le    := fun e _ => keyLE_sentinel e.1
      hpushed_le := fun k hk => absurd hk (Nat.not_le.mpr k.isLt) }
  let pq := process_queue O ⟨.inl false, .inl false⟩ (.inl false) ps₁.state.size
              sorted ps₁ inv₁ hbounds_sorted
              -- hcurptr_sem: sentinel key never matches any real entry (key.1 ≠ key.2 for all entries).
              (fun entry hmem heq => absurd heq (sentinel_no_match sorted hnonred_sorted entry hmem))
              -- hec: entry-correctness for all sorted entries.
              hec_sorted
              si
  ⟨pq.1, pq.2.1, by
    -- Every j ∈ vlist[i] ends up with ids[j].isSome:
    -- either it was resolved as redundant by populate_queue (hpost₁ right branch),
    -- or it was enqueued and process_queue set it (hpost₁ left branch + pq.2.2.2).
    intro j hmem hreach
    have h := hpost₁ j hmem
    cases h with
    | inl hqueue =>
      obtain ⟨key, hmem_q⟩ := hqueue
      -- j was enqueued; sorting is a permutation, so it's still in sorted.
      have hmem_sorted : (key, j) ∈ sorted := List.Perm.mem_iff
        (List.mergeSort_perm _ _) |>.mpr hmem_q
      exact pq.2.2.2.1 ⟨key, j⟩ hmem_sorted
    | inr hset =>
      -- j was already resolved; process_queue is monotone for isSome.
      exact pq.2.2.1 j hset,
   -- VarInvariant: from process_queue's return.
   pq.2.2.2.2.1,
   -- AllAbove (i.1 - 1): process_queue returns `i ≤ va` for every node; with 0 < i that gives i-1 < va.
   fun hipos k => by have h := pq.2.2.2.2.2.2 k; omega,
   -- HeapInjective: from process_queue's return.
   pq.2.2.2.2.2.1⟩
lemma invariant_step_down {n m : Nat} {O : OBdd n m} {ps : ProvedState n m}
    {i : Nat}
    (inv  : Invariant O ps i)
    (hset : ∀ (j : Fin m), O.1.heap[j].var.1 = i →
              Reachable O.1.heap O.1.root (.node j) → (ps.state.ids[j]).isSome)
    (hi   : 0 < i) :
    Invariant O ps (i - 1) :=
  ⟨fun j hj hreach => by
     have h : i ≤ O.1.heap[j].var.1 := by omega
     rcases h.eq_or_lt with h_eq | h_lt
     · exact hset j h_eq.symm hreach
     · exact inv.1 j h_lt hreach,
   inv.2⟩
structure RootCorrect {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (ptr : RawPointer) :
    Prop where
  hptr  : ptr.Bounded ps.state.size
  ho    : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩
  hred  : OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩, ho⟩
  heval : ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩, ho⟩ I =
               O.evaluate I
def loop_helper {n m : Nat} (O : OBdd n m) (r : Fin m)
    (hr    : O.1.root = .node r)
    (vlist : Vector (List (Fin m)) n)
    (hdiscover : ∀ (j : Fin m),
        Reachable O.1.heap O.1.root (.node j) →
        j ∈ vlist[O.1.heap[j].var])
    (hdiscover_inv : ∀ (j : Fin m) (ii : Fin n),
        j ∈ vlist[ii] →
        O.1.heap[j].var.1 = ii.1 ∧ Reachable O.1.heap O.1.root (.node j))
    (i    : Fin n)
    (h_le : O.1.heap[r].var.1 ≤ i.1)
    (ps : ProvedState n m) (inv : Invariant O ps i.1)
    (hvarinv : VarInvariant O ps) (hallabove : AllAbove ps i.1)
    (hheapinj : HeapInjective ps) :
    { ps' : ProvedState n m //
        (ps'.state.ids[r]).isSome ∧
        ∀ (ptr : RawPointer), ps'.state.ids[r] = some ptr → RootCorrect O ps' ptr } :=
  let ⟨ps₁, inv₁, hset₁, hvarinv₁, hallabove₁, hheapinj₁⟩ :=
    step O vlist i ps inv (fun j hj => hdiscover_inv j i hj)
    hvarinv hallabove hheapinj
  match h : i.1 - O.1.heap[r].var.1 with
  | Nat.zero =>
    have hi_eq  : O.1.heap[r].var = i :=
      Fin.ext (Nat.le_antisymm h_le (Nat.le_of_sub_eq_zero h))
    have hr_in  : r ∈ vlist[i] := by
      simp only [← hi_eq]
      exact hdiscover r (by rw [← hr]; exact .refl)
    have hrisSome : (ps₁.state.ids[r]).isSome :=
      hset₁ r hr_in (by rw [← hr]; exact .refl)
    ⟨ps₁, hrisSome, fun ptr hkptr =>
      let ⟨hj, hptr, ho, hred, heval⟩ := inv₁.2 r ptr hkptr
      ⟨hptr, ho, hred, fun I => (heval I).trans
        (congrArg (OBdd.evaluate · I)
          (Subtype.ext
            (congrArg (fun root => ({ heap := O.1.heap, root } : Bdd n m)) hr.symm)))⟩⟩
  | Nat.succ j =>
    have hlt    : j + O.1.heap[r].var.1 < n := by
      have := i.isLt; simp only [Nat.succ_eq_add_one] at h; omega
    have hi_pos : 0 < i.1 := by omega
    have inv₁' : Invariant O ps₁ (j + O.1.heap[r].var.1) := by
      have hbase := invariant_step_down inv₁
        (fun k hk hreach => hset₁ k (Fin.ext hk ▸ hdiscover k hreach) hreach)
        hi_pos
      simp only [Nat.succ_eq_add_one] at h
      convert hbase using 1; omega
    loop_helper O r hr vlist hdiscover hdiscover_inv
      ⟨j + O.1.heap[r].var.1, hlt⟩ (Nat.le_add_left _ _) ps₁ inv₁'
      hvarinv₁
      (by
        have hab := hallabove₁ hi_pos
        simp only [Nat.succ_eq_add_one] at h
        have heq : i.1 - 1 = j + O.1.heap[r].var.1 := by omega
        show AllAbove ps₁ (j + O.1.heap[r].var.1)
        rw [← heq]; exact hab)
      hheapinj₁
termination_by i.1 - O.1.heap[r].var.1
decreasing_by simp_all
def zero_vars_to_bool : Bdd 0 m → Bool
  | B => match B.root with
    | .terminal b => b
    | .node j     => False.elim (Nat.not_lt_zero _ B.heap[j].var.2)
def oreduce (O : OBdd n m) :
    { p : (s : Nat) × OBdd n s // OBdd.Reduced p.2 ∧ p.2.evaluate = O.evaluate } :=
  match n with
  | .zero =>
    match hroot : O.1.root with
    | .terminal b =>
      ⟨⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.Ordered_of_terminal⟩⟩,
       Bdd.reduced_of_terminal,
       OBdd.evaluate_terminal.trans (OBdd.evaluate_terminal' hroot).symm⟩
    | .node j => absurd O.1.heap[j].var.isLt (Nat.not_lt_zero _)
  | .succ nn =>
    match hroot : O.1.root with
    | .terminal b =>
      ⟨⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.Ordered_of_terminal⟩⟩,
       Bdd.reduced_of_terminal,
       OBdd.evaluate_terminal.trans (OBdd.evaluate_terminal' hroot).symm⟩
    | .node r =>
      let ⟨ps, hrisSome, hcorr⟩ :=
        loop_helper O r hroot (OBdd.discover O)
          (fun j hj => OBdd.discover_spec hj)
          (fun j ii hj => OBdd.discover_spec_inv hj)
          ⟨nn, Nat.lt_add_one nn⟩ (Nat.lt_succ_iff.mp O.1.heap[r].var.isLt)
          (provedStateInitial (nn + 1) m)
          (inv_initial (fun j => Nat.lt_succ_iff.mp O.1.heap[j].var.isLt))
          varInvariant_initial allAbove_initial heapInjective_initial
      let rid  := (ps.state.ids[r]).get hrisSome
      let rc   := hcorr rid (Option.get_mem hrisSome)
      ⟨⟨ps.state.size, ⟨⟨cook_heap ps.state.heap ps.hh, rid.cook rc.hptr⟩, rc.ho⟩⟩,
       rc.hred, funext rc.heval⟩
end Reduce


