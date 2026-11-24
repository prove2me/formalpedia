-- Prove2me | Definitions.Def_CSL_Circuit_Framework_AffineStreams
-- name    : CSL_Circuit_Framework_AffineStreams
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:44:12.901138+00:00
-- url     : https://prove2.me/theorems/83a0f2f9-b8db-4f95-997d-09066dd4f0a0
-- title:
--   Coded sorting library: Circuit / Framework / AffineStreams
-- statement:
--   Module `CodedSorting.Circuit.Framework.AffineStreams` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Concrete buffered implementations of permutations with finitely many
--   increasing address streams. Costs count actual block transfers.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Framework.AffineStreams

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_BucketReader
import Definitions.Def_CSL_Shared_Indexing_SequentialArithmetic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange

/-! Concrete buffered implementations of permutations with finitely many
increasing address streams. Costs count actual block transfers. -/

namespace CSL.AffineStreams

open BucketMachine BucketReader SequentialArithmetic

variable {Q K : ℕ}

/-- Original source addresses, in their new output-address order. -/
def targetSources (e : Equiv.Perm (Fin Q)) : List (Fin Q) :=
  (List.finRange Q).map e.symm

theorem targetSources_perm (e : Equiv.Perm (Fin Q)) :
    (targetSources e).Perm (List.finRange Q) := Equiv.Perm.map_finRange_perm e.symm

theorem targetSources_destinations (e : Equiv.Perm (Fin Q)) :
    (targetSources e).map e = List.finRange Q := by
  simp [targetSources, List.map_map, Function.comp_def]

/-- For each stream, input order and output order agree because the destination
map is increasing within that stream. This is the missing scheduling fact. -/
theorem increasing_stream_fibers (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x < y → key x = key y → e x < e y) (k : Fin K) :
    bucket key (List.finRange Q) k = bucket key (targetSources e) k := by
  have hp : (bucket key (List.finRange Q) k).Perm (bucket key (targetSources e) k) :=
    (targetSources_perm e).symm.filter _
  have hi : (bucket key (List.finRange Q) k).Pairwise (fun x y => e x < e y) := by
    have hs := (List.pairwise_lt_finRange Q).sublist (bucket_sublist key _ k)
    exact hs.imp_of_mem (fun {x y} hx hy hxy =>
      hinc x y hxy (((mem_bucket key _ k x).mp hx).2.trans
        ((mem_bucket key _ k y).mp hy).2.symm))
  have ht : ((bucket key (targetSources e) k).map e).Pairwise (· < ·) := by
    have hs : ((targetSources e).map e).Pairwise (· < ·) := by
      rw [targetSources_destinations]
      exact List.pairwise_lt_finRange Q
    exact hs.sublist ((bucket_sublist key (targetSources e) k).map e)
  have heq := List.eq_of_perm_of_sorted (hp.map e) (List.pairwise_map.mpr hi) ht
  exact (List.map_injective_iff.mpr e.injective) heq

/-- An actual K-reader schedule implements the permutation, with K block buffers
and at most 4 floor(Q/B)+2K+2 block transfers. -/
theorem increasing_stream_reconstruction (e : Equiv.Perm (Fin Q))
    (key : Fin Q → Fin K)
    (hinc : ∀ x y, x < y → key x = key y → e x < e y)
    (B : ℕ) (hB : 0 < B) :
    ∃ final, readSchedule ((targetSources e).map key)
        (initialReaders key B (List.finRange Q)) = some (targetSources e, final) ∧
      completeTransfers key B hB (List.finRange Q) (targetSources e) final ≤
        4 * (Q / B) + 2 * K + 2 ∧ occupiedReaders final ≤ K * B := by
  simpa only [List.length_finRange] using
    complete_reconstruction_bound key B hB (List.finRange Q) (targetSources e)
      (increasing_stream_fibers e key hinc)

/-- Fixed integer multiplication modulo Q now has a real buffered algorithm,
not merely a decomposition into monotone runs. -/
theorem multiplication_reconstruction {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hcoprime : a.Coprime Q) (B : ℕ) (hB : 0 < B) :
    ∃ final, readSchedule
        ((targetSources (multiplicationEquiv hQ hcoprime)).map (multiplicationRun ha hQ))
        (initialReaders (multiplicationRun ha hQ) B (List.finRange Q)) =
        some (targetSources (multiplicationEquiv hQ hcoprime), final) ∧
      completeTransfers (multiplicationRun ha hQ) B hB (List.finRange Q)
        (targetSources (multiplicationEquiv hQ hcoprime)) final ≤
        4 * (Q / B) + 2 * a + 2 ∧ occupiedReaders final ≤ a * B := by
  apply increasing_stream_reconstruction (multiplicationEquiv hQ hcoprime)
    (multiplicationRun ha hQ) _ B hB
  intro x y hxy hr
  exact multiplication_increasing_in_run ha hQ x y hxy hr

/-- Reversing an increasing-stream permutation keeps the same stream bound:
classify an output address by the stream of its unique preimage. -/
theorem inverse_increasing_streams (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x < y → key x = key y → e x < e y) :
    ∀ x y, x < y → key (e.symm x) = key (e.symm y) → e.symm x < e.symm y := by
  intro x y hxy hkey
  rcases lt_trichotomy (e.symm x) (e.symm y) with hlt | heq | hgt
  · exact hlt
  · have hsame : x = y := e.symm.injective heq
    exact (ne_of_lt hxy hsame).elim
  · have hyx := hinc (e.symm y) (e.symm x) hgt hkey.symm
    have : y < x := by simpa using hyx
    exact (lt_asymm hxy this).elim

/-- Inverse multiplication has the same a-buffer implementation. -/
theorem inverse_multiplication_reconstruction {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hcoprime : a.Coprime Q) (B : ℕ) (hB : 0 < B) :
    let e := multiplicationEquiv hQ hcoprime
    let key := fun x => multiplicationRun ha hQ (e.symm x)
    ∃ final, readSchedule ((targetSources e.symm).map key)
        (initialReaders key B (List.finRange Q)) = some (targetSources e.symm, final) ∧
      completeTransfers key B hB (List.finRange Q) (targetSources e.symm) final ≤
        4 * (Q / B) + 2 * a + 2 ∧ occupiedReaders final ≤ a * B := by
  try dsimp only
  apply increasing_stream_reconstruction _ _ _ B hB
  apply inverse_increasing_streams
  exact fun x y hxy hr => multiplication_increasing_in_run ha hQ x y hxy hr

theorem addOffset_injective (c : Fin Q) : Function.Injective (addOffset c) := by
  letI : NeZero Q := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt c.isLt)⟩
  intro x y h
  have hz : ((x.val + c.val : ℕ) : ZMod Q) = ((y.val + c.val : ℕ) : ZMod Q) := by
    apply ZMod.val_injective Q
    simpa only [ZMod.val_natCast, addOffset] using congrArg Fin.val h
  rw [Nat.cast_add, Nat.cast_add] at hz
  have hv := congrArg ZMod.val (add_right_cancel hz)
  apply Fin.ext
  simpa only [ZMod.val_natCast_of_lt x.isLt, ZMod.val_natCast_of_lt y.isLt] using hv

noncomputable def additionEquiv (c : Fin Q) : Equiv.Perm (Fin Q) :=
  Equiv.ofBijective (addOffset c) ((Finite.injective_iff_bijective).1 (addOffset_injective c))

theorem addition_reconstruction (c : Fin Q) (B : ℕ) (hB : 0 < B) :
    ∃ final, readSchedule ((targetSources (additionEquiv c)).map (additionRun c))
        (initialReaders (additionRun c) B (List.finRange Q)) =
        some (targetSources (additionEquiv c), final) ∧
      completeTransfers (additionRun c) B hB (List.finRange Q)
        (targetSources (additionEquiv c)) final ≤
        4 * (Q / B) + 6 ∧ occupiedReaders final ≤ 2 * B := by
  apply increasing_stream_reconstruction (additionEquiv c) (additionRun c) _ B hB
  exact fun x y hxy hr => addition_increasing_in_run c x y hxy hr

section Payloads

variable {Value : Type*}

def inputRecords (F : Fin Q → Value) : List (Fin Q × Value) :=
  (List.finRange Q).map (fun i => (i, F i))

def targetRecords (e : Equiv.Perm (Fin Q)) (F : Fin Q → Value) : List (Fin Q × Value) :=
  (targetSources e).map (fun i => (i, F i))

theorem record_bucket (key : Fin Q → Fin K) (F : Fin Q → Value)
    (xs : List (Fin Q)) (k : Fin K) :
    bucket (fun x : Fin Q × Value => key x.1) (xs.map (fun i => (i, F i))) k =
      (bucket key xs k).map (fun i => (i, F i)) := by
  simp only [bucket, List.filter_map, Function.comp_def]

theorem targetRecords_payloads (e : Equiv.Perm (Fin Q)) (F : Fin Q → Value) :
    (targetRecords e F).map Prod.snd = (List.finRange Q).map (fun y => F (e.symm y)) := by
  simp [targetRecords, targetSources, List.map_map, Function.comp_def]

/-- The same concrete block execution moves arbitrary payloads attached to source
addresses; the output payload at destination y is the original F(e^{-1}(y)). -/
theorem payload_reconstruction (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x < y → key x = key y → e x < e y)
    (F : Fin Q → Value) (B : ℕ) (hB : 0 < B) :
    ∃ final, readSchedule ((targetRecords e F).map (fun x => key x.1))
        (initialReaders (fun x => key x.1) B (inputRecords F)) =
        some (targetRecords e F, final) ∧
      completeTransfers (fun x => key x.1) B hB (inputRecords F) (targetRecords e F) final ≤
        4 * (Q / B) + 2 * K + 2 ∧ occupiedReaders final ≤ K * B := by
  have hf : ∀ k, bucket (fun x : Fin Q × Value => key x.1) (inputRecords F) k =
      bucket (fun x : Fin Q × Value => key x.1) (targetRecords e F) k := by
    intro k
    simp only [inputRecords, targetRecords, record_bucket]
    rw [increasing_stream_fibers e key hinc k]
  simpa only [inputRecords, List.length_map, List.length_finRange] using
    complete_reconstruction_bound (fun x : Fin Q × Value => key x.1) B hB
      (inputRecords F) (targetRecords e F) hf

/-- A specialization with K=a, independent of Q and of the payloads. -/
theorem multiplication_payload_reconstruction {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hcoprime : a.Coprime Q) (F : Fin Q → Value) (B : ℕ) (hB : 0 < B) :
    ∃ final, readSchedule
        ((targetRecords (multiplicationEquiv hQ hcoprime) F).map
          (fun x => multiplicationRun ha hQ x.1))
        (initialReaders (fun x => multiplicationRun ha hQ x.1) B (inputRecords F)) =
        some (targetRecords (multiplicationEquiv hQ hcoprime) F, final) ∧
      completeTransfers (fun x => multiplicationRun ha hQ x.1) B hB (inputRecords F)
        (targetRecords (multiplicationEquiv hQ hcoprime) F) final ≤
        4 * (Q / B) + 2 * a + 2 ∧ occupiedReaders final ≤ a * B := by
  apply payload_reconstruction (multiplicationEquiv hQ hcoprime)
    (multiplicationRun ha hQ) _ F B hB
  intro x y hxy hr
  exact multiplication_increasing_in_run ha hQ x y hxy hr

end Payloads

end CSL.AffineStreams


