-- Prove2me | Definitions.Def_CSL_Sorting_SmallMemory_NarrowWords_PublicUnrolledComplete
-- name    : CSL_Sorting_SmallMemory_NarrowWords_PublicUnrolledComplete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:57:10.058537+00:00
-- url     : https://prove2.me/theorems/f84f5783-74ab-472c-a7c6-1752b94f3b11
-- title:
--   Coded sorting library: Sorting / SmallMemory / NarrowWords / PublicUnrolledComplete
-- statement:
--   Module `CodedSorting.Sorting.SmallMemory.NarrowWords.PublicUnrolledComplete` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Capacity for the public-unrolled general-word sorter
--
--   The counter uses `c + 1` digits: `c` digits need not represent the count
--   `N` when `N = (2^w)^c`. These arithmetic statements do not make any claim
--   about how a public schedule or its program position is represented.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.SmallMemory.NarrowWords.PublicUnrolledComplete

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Words_WordConvention
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Sort
import Definitions.Def_CSL_Sorting_SmallMemory_NarrowWords_Histogram
import Definitions.Def_CSL_Sorting_SmallMemory_Radix_Sort

section Capacity
/-!
# Capacity for the public-unrolled general-word sorter

The counter uses `c + 1` digits: `c` digits need not represent the count
`N` when `N = (2^w)^c`. These arithmetic statements do not make any claim
about how a public schedule or its program position is represented.
-/

set_option autoImplicit false
namespace CSL.TwoWordGeneralCapacity

theorem positive_width (N w c : ℕ) (hn : 2 ≤ N)
    (hc : Nat.clog 2 N ≤ c * w) : 0 < w ∧ 0 < c :=
  WordConvention.positive_words N w c hn hc

theorem counter_capacity (N w c : ℕ) (hw : 0 < w)
    (hc : Nat.clog 2 N ≤ c * w) : N < (2^w)^(c+1) := by
  have hcap := WordConvention.covers_capacity N w c hc
  have hb : 1 < 2^w := Nat.one_lt_two_pow hw.ne'
  have hp : 0 < (2^w)^c := by positivity
  rw [pow_succ]
  nlinarith

theorem counter_capacity_of_covers (N w c : ℕ) (hn : 2 ≤ N)
    (hc : Nat.clog 2 N ≤ c * w) : N < (2^w)^(c+1) :=
  counter_capacity N w c (positive_width N w c hn hc).1 hc

theorem alphabet_lt_length (N w : ℕ) (hsmall : w < Nat.clog 2 N) :
    2^w < N := by
  by_contra h
  have hcap : N ≤ 2^w := by omega
  have hlog : Nat.clog 2 N ≤ w :=
    (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).1 hcap
  omega

theorem scan_bound (N w c : ℕ) (hsmall : w < Nat.clog 2 N) :
    (c+1) * (N+2^w) ≤ 2 * (c+1) * N := by
  have h := alphabet_lt_length N w hsmall
  nlinarith

end CSL.TwoWordGeneralCapacity
end Capacity

section OutputList
/-!
# Canonical sorted output from finite-alphabet counts

This pure list bridge is independent of any counter representation or machine
execution. Its alphabet is `Fin K`; a `w`-bit machine uses `K = 2^w`.
`emit_min` is the exact ghost-state update needed by a loop which emits the
least key with positive count and then decrements that count by one.
-/

set_option autoImplicit false

namespace CSL.TwoWordGeneralOutputList

variable {K : ℕ}

def sortedCounts (counts : Fin K → ℕ) : List (Fin K) :=
  (List.finRange K).flatMap fun key => List.replicate (counts key) key

theorem length (counts : Fin K → ℕ) :
    (sortedCounts counts).length = ∑ key, counts key := by
  simp only [sortedCounts,List.length_flatMap,List.length_replicate]
  exact (Fin.sum_univ_def counts).symm

theorem sorted (counts : Fin K → ℕ) :
    (sortedCounts counts).Sorted (· ≤ ·) := by
  change ((List.finRange K).flatMap _).Pairwise (· ≤ ·)
  rw [List.pairwise_flatMap]
  refine ⟨fun key _ => List.sorted_le_replicate (counts key) key,?_⟩
  apply (List.pairwise_le_finRange K).imp
  intro a b hab x hx y hy
  simpa only [List.eq_of_mem_replicate hx,List.eq_of_mem_replicate hy] using hab

theorem count (counts : Fin K → ℕ) (key : Fin K) :
    (sortedCounts counts).count key = counts key := by
  simp only [sortedCounts,List.count_flatMap,Function.comp_def,List.count_replicate]
  rw [←Fin.sum_univ_def]
  simp

theorem mem_iff (counts : Fin K → ℕ) (key : Fin K) :
    key ∈ sortedCounts counts ↔ 0 < counts key := by
  rw [←List.count_pos_iff,count]

theorem perm_of_counts (counts : Fin K → ℕ) (xs : List (Fin K))
    (hcounts : ∀ key, counts key = xs.count key) :
    (sortedCounts counts).Perm xs := by
  apply List.perm_iff_count.mpr
  intro key
  rw [count,hcounts]

theorem counts_of_perm (counts : Fin K → ℕ) (xs : List (Fin K))
    (hperm : (sortedCounts counts).Perm xs) :
    ∀ key, counts key = xs.count key := by
  intro key
  simpa only [count] using List.perm_iff_count.mp hperm key

theorem correct (counts : Fin K → ℕ) (xs : List (Fin K))
    (hcounts : ∀ key, counts key = xs.count key) :
    (sortedCounts counts).Sorted (· ≤ ·) ∧ (sortedCounts counts).Perm xs :=
  ⟨sorted counts,perm_of_counts counts xs hcounts⟩

theorem unique (counts : Fin K → ℕ) (xs : List (Fin K))
    (hcounts : ∀ key, counts key = xs.count key)
    (hsorted : xs.Sorted (· ≤ ·)) : sortedCounts counts = xs :=
  List.eq_of_perm_of_sorted (perm_of_counts counts xs hcounts) (sorted counts) hsorted

theorem nil_iff (counts : Fin K → ℕ) :
    sortedCounts counts = [] ↔ ∀ key, counts key = 0 := by
  constructor
  · intro h key
    rw [←count counts key,h]
    rfl
  · intro h
    simp [sortedCounts,h]

theorem lower_bound (counts : Fin K → ℕ) (a : Fin K)
    (hlower : ∀ key, key < a → counts key = 0) :
    ∀ key ∈ sortedCounts counts, a ≤ key := by
  intro key hkey
  by_contra h
  have hz := hlower key (lt_of_not_ge h)
  have hp := (mem_iff counts key).mp hkey
  omega

/-- Emitting the least remaining key removes exactly the first list element. -/
theorem emit_min (counts : Fin K → ℕ) (a : Fin K)
    (ha : 0 < counts a) (hlower : ∀ key, key < a → counts key = 0) :
    sortedCounts counts =
      a :: sortedCounts (Function.update counts a (counts a - 1)) := by
  refine List.eq_of_perm_of_sorted ?_ (sorted counts) ?_
  · apply List.perm_iff_count.mpr
    intro key
    by_cases hkey : key = a
    · subst key
      simp only [count,List.count_cons_self,Function.update_self]
      omega
    · simp [count,List.count_cons,hkey,Ne.symm hkey,Function.update_of_ne hkey]
  · rw [List.sorted_cons]
    refine ⟨lower_bound _ a ?_,sorted _⟩
    intro key hkey
    simpa [Function.update_of_ne (ne_of_lt hkey)] using hlower key hkey

theorem length_after_emit (counts : Fin K → ℕ) (a : Fin K)
    (ha : 0 < counts a) (hlower : ∀ key, key < a → counts key = 0) :
    (sortedCounts (Function.update counts a (counts a - 1))).length + 1 =
      (sortedCounts counts).length := by
  rw [emit_min counts a ha hlower]
  rfl

/-- The standard emitted-prefix invariant advances by an actual emitted key. -/
theorem emitted_prefix_step (initial emitted : List (Fin K)) (counts : Fin K → ℕ)
    (a : Fin K) (ha : 0 < counts a)
    (hlower : ∀ key, key < a → counts key = 0)
    (hprefix : initial = emitted ++ sortedCounts counts) :
    initial = (emitted ++ [a]) ++
      sortedCounts (Function.update counts a (counts a - 1)) := by
  rw [hprefix,emit_min counts a ha hlower]
  simp only [List.append_assoc,List.singleton_append]

end CSL.TwoWordGeneralOutputList
end OutputList

section PublicUnrolled
/-!
# Counting sort with a public unrolled input/output schedule

All input-dependent keys and counter digits are in two resident words or
on the word disk. The list of stages, including the N fixed output
addresses, depends only on public parameters. Its program position is
governed by the existing Stage semantics, not encoded in a resident word.
Consequently this endpoint explicitly uses a public-size unrolled program;
it is not a constant-size uniform-program or fully charged-control theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CSL.TwoWordGeneralPublicUnrolled
open TwoWordPhysicalAddresses TwoWordGeneralCounter TwoWordRadixPreparedBuild
open TwoWordGeneralHistogram TwoWordGeneralOutput TwoWordGeneralOutputEmit

noncomputable def outputStages (w : ℕ) (hw : 0 < w) (d start : ℕ) : ℕ → List (Stage (Word w))
  | 0 => []
  | count+1 => searchStages w hw d ++
      [.straight (emitCode w hw d start)] ++ outputStages w hw d (start+1) count

def slope (d : ℕ) : ℕ := 20 * (d+1)

theorem output_complete (w : ℕ) (hw : 0 < w) (d start : ℕ)
    (s : State (Word w)) (xs : List (Word w))
    (hhist : Histogram d s.disk xs) (hsorted : xs.Sorted (· ≤ ·))
    (hcursor : ∀ x ∈ xs, s.disk 0 ≤ x) :
    ∃ t cost, Executes (outputStages w hw d start xs.length) s t cost ∧
      File t.disk (inputBase w d + start) xs ∧
      (∀ a, inputBase w d ≤ a →
        (a < inputBase w d + start ∨ inputBase w d + start + xs.length ≤ a) →
        t.disk a = s.disk a) ∧
      cost + slope d * (s.disk 0).val ≤ slope d * (xs.length + (t.disk 0).val) := by
  induction xs generalizing start s with
  | nil =>
    refine ⟨s, 0, .done s, ?_, ?_, ?_⟩
    · intro i hi; simp at hi
    · intro a ha hr; rfl
    · simp
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.sorted_cons.mp hsorted
    have hcur : (s.disk 0).val ≤ x.val := hcursor x (by simp)
    have hzero : ∀ key : Word w, (s.disk 0).val ≤ key.val → key.val < x.val →
        value w key 0 d s.disk = 0 := by
      intro key hlo hhi
      rw [hhist]
      apply List.count_eq_zero.mpr
      intro hm
      rcases List.mem_cons.mp hm with he | hm
      · subst key; omega
      · have := hhead key hm; change x.val ≤ key.val at this; omega
    have hpos : 0 < value w x 0 d s.disk := by
      rw [hhist, List.count_cons_self]
      omega
    obtain ⟨found, hsearch, hkey, hvalues, hframe⟩ :=
      search_complete w hw d s x hcur hzero hpos
    let mid := emit w hw d start found
    have hmidkey : mid.disk 0 = x := (emit_key w hw d start found).trans hkey
    have hmid : Histogram d mid.disk xs := by
      intro key
      have hp : 0 < value w (found.disk 0) 0 d found.disk := by
        rw [hkey, hvalues]; exact hpos
      by_cases he : key = x
      · subst key
        have hv := emit_selected w hw d start found hp
        rw [hkey, hvalues, hhist, List.count_cons_self] at hv
        simpa only [mid, Nat.add_sub_cancel] using hv
      · have hv := emit_other w hw d start found key (by simpa only [hkey] using he)
        rw [hvalues, hhist] at hv
        simpa [mid, List.count_cons, he, Ne.symm he] using hv
    have hnext : ∀ key ∈ xs, mid.disk 0 ≤ key := by
      intro key hk
      rw [hmidkey]
      exact hhead key hk
    obtain ⟨t, tailCost, hrun, hfile, htailframe, hcost⟩ :=
      ih (start+1) mid hmid htail hnext
    let totalCost := searchCost d (s.disk 0) x + (3+6*d) + tailCost
    refine ⟨t, totalCost, ?_, ?_, ?_, ?_⟩
    · have hemit : Executes [.straight (emitCode w hw d start)] found mid (3+6*d) := by
        have he := Executes.straight (emitCode w hw d start) [] found mid 0
          (by simpa only [execute_emit] using Executes.done mid)
        simpa only [emit_cost, Nat.add_zero] using he
      have ha := TwoWordRadixPass.executes_append
        (TwoWordRadixPass.executes_append hsearch hemit) hrun
      simpa only [List.length_cons, outputStages, totalCost, List.append_assoc] using ha
    · intro j hj
      cases j with
      | zero =>
        have hf := htailframe (inputBase w d+start) (by omega) (Or.inl (by omega))
        have he := emit_output w hw d start found
        simpa only [Nat.add_zero, List.getElem_cons_zero, mid, hkey] using hf.trans he
      | succ j =>
        have hf := hfile j (by simp only [List.length_cons] at hj; omega)
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
          List.getElem_cons_succ] using hf
    · intro a ha hr
      have hne : a ≠ inputBase w d+start := by
        simp only [List.length_cons] at hr
        omega
      have hf := htailframe a ha (by simp only [List.length_cons] at hr; omega)
      have he := emit_frame w hw d start found a ha hne
      have hs := hframe a (by unfold inputBase at ha; omega)
        (by unfold inputBase at ha; omega) (by unfold inputBase flagAddress at *; omega)
      exact hf.trans (he.trans hs)
    · have hs := searchCost_le d (s.disk 0) x
      rw [hmidkey] at hcost
      have hdiff : x.val - (s.disk 0).val + (s.disk 0).val = x.val := Nat.sub_add_cancel hcur
      try dsimp only [totalCost, slope] at *
      simp only [List.length_cons]
      nlinarith only [hcost, hs, hdiff]

def resetCode (w : ℕ) : List (Command (Word w)) :=
  [.localOp (fun _ => (0,0)), .writeLeft 0]

noncomputable def code (w : ℕ) (hw : 0 < w) (d n : ℕ) : List (Stage (Word w)) :=
  [.straight (histogramCode w hw d n), .straight (resetCode w)] ++
    outputStages w hw d 0 n

def output (w : ℕ) (xs : List (Word w)) : List (Word w) :=
  TwoWordGeneralOutputList.sortedCounts (fun key => xs.count key)

def budget (w d n : ℕ) : ℕ := 100 * (d+1) * (n + 2^w + 1)

end CSL.TwoWordGeneralPublicUnrolled
end PublicUnrolled

section Footprint
/-! Syntactic finite disk allocation for the publicly unrolled counting
program. Bounds hold for every resident state and cover reads and writes.
The immutable public code and its interpreter position are not counted as
data cells; this is the explicitly stated public-program convention. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CSL.TwoWordGeneralFootprint
open TwoWordPhysicalAddresses TwoWordGeneralCounter
open TwoWordRadixFootprint (BoundedCommand BoundedStage BoundedCode)

def space (w d n : ℕ) : ℕ := 3+d*2^w+n
def CommandsBound {w : ℕ} (L : ℕ) (code : List (Command (Word w))) : Prop :=
  ∀cmd∈code,BoundedCommand L cmd

theorem append {w L : ℕ} (a b : List (Command (Word w)))
    (ha : CommandsBound L a) (hb : CommandsBound L b) : CommandsBound L (a++b) := by
  intro cmd hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ha cmd hc
  · exact hb cmd hc

theorem digit_bound (w d n j : ℕ) (hj : j<d)
    (f : Word w × Word w → Word w × Word w) :
    CommandsBound (space w d n) (digitCode w j f) := by
  intro cmd hc
  simp only [digitCode,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 0<space w d n
    unfold space;omega
  · intro r
    have := TwoWordGeneralHistogram.address_below w d j r.1 hj
    change address w j r.1<space w d n
    unfold space;omega
  · change 1<space w d n
    unfold space;omega
  · trivial
  · change 1<space w d n
    unfold space;omega
  · change 0<space w d n
    unfold space;omega
  · intro r
    have := TwoWordGeneralHistogram.address_below w d j r.1 hj
    change address w j r.1<space w d n
    unfold space;omega

theorem counter_bound (w d n start count : ℕ) (hc : start+count≤d)
    (f : Word w × Word w → Word w × Word w) :
    CommandsBound (space w d n) (TwoWordGeneralCounter.code w start f count) := by
  induction count generalizing start with
  | zero => intro cmd h; simp [TwoWordGeneralCounter.code] at h
  | succ count ih =>
    exact append _ _ (digit_bound w d n start (by omega) f)
      (ih (start+1) (by omega))

theorem zero_bound (w L start count : ℕ) (hc : start+count≤L) :
    CommandsBound L (TwoWordGeneralHistogram.zeroCode w start count) := by
  induction count generalizing start with
  | zero => intro cmd h; simp [TwoWordGeneralHistogram.zeroCode] at h
  | succ count ih =>
    apply append _ _ ?_ (ih (start+1) (by omega))
    intro cmd h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl
    · trivial
    · change start<L;omega

theorem set_key_bound (w : ℕ) (hw : 0<w) (d n input : ℕ)
    (hi : input<space w d n) :
    CommandsBound (space w d n) (TwoWordGeneralHistogram.setKeyCode w hw input) := by
  intro cmd hc
  simp only [TwoWordGeneralHistogram.setKeyCode,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact hi
  · change 0<space w d n;unfold space;omega
  · trivial
  · change 1<space w d n;unfold space;omega

theorem increment_bound (w : ℕ) (hw : 0<w) (d n input : ℕ)
    (hi : input<space w d n) :
    CommandsBound (space w d n)
      (TwoWordGeneralHistogram.incrementCode w hw d input) :=
  append _ _ (set_key_bound w hw d n input hi)
    (counter_bound w d n 0 d (by omega) _)

theorem scan_bound (w : ℕ) (hw : 0<w) (d n start count : ℕ)
    (hc : start+count≤space w d n) :
    CommandsBound (space w d n)
      (TwoWordGeneralHistogram.scanCode w hw d start count) := by
  induction count generalizing start with
  | zero => intro cmd h;simp [TwoWordGeneralHistogram.scanCode] at h
  | succ count ih =>
    exact append _ _ (increment_bound w hw d n start (by omega))
      (ih (start+1) (by omega))

theorem histogram_bound (w : ℕ) (hw : 0<w) (d n : ℕ) :
    CommandsBound (space w d n) (TwoWordGeneralHistogram.histogramCode w hw d n) :=
  append _ _ (zero_bound w _ 2 (d*2^w) (by unfold space;omega))
    (scan_bound w hw d n _ n (by unfold TwoWordGeneralHistogram.inputBase space;omega))

theorem test_bound (w : ℕ) (hw : 0<w) (d n : ℕ) :
    CommandsBound (space w d n) (TwoWordGeneralOutput.testCode w hw d) := by
  apply append _ _ (append _ _ ?_ (counter_bound w d n 0 d (by omega) _)) ?_
  · intro cmd hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · trivial
    · change 1<space w d n;unfold space;omega
  · intro cmd hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · change 1<space w d n;unfold space;omega
    · trivial
    · change TwoWordGeneralOutput.flagAddress w d<space w d n
      unfold TwoWordGeneralOutput.flagAddress space;omega

theorem advance_bound (w d n : ℕ) :
    CommandsBound (space w d n) (TwoWordGeneralOutput.advanceCode w) := by
  intro cmd hc
  simp only [TwoWordGeneralOutput.advanceCode,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl
  · change 0<space w d n;unfold space;omega
  · trivial
  · change 0<space w d n;unfold space;omega

theorem search_bound (w : ℕ) (hw : 0<w) (d n : ℕ) :
    BoundedStage (space w d n) (.loop (TwoWordGeneralOutput.searchProgram w hw d)) := by
  constructor
  · change TwoWordGeneralOutput.flagAddress w d<space w d n
    unfold TwoWordGeneralOutput.flagAddress space;omega
  · exact append _ _ (advance_bound w d n) (test_bound w hw d n)

theorem search_stages_bound (w : ℕ) (hw : 0<w) (d n : ℕ) :
    BoundedCode (space w d n) (TwoWordGeneralOutput.searchStages w hw d) := by
  intro st hs
  simp only [TwoWordGeneralOutput.searchStages,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl
  · exact test_bound w hw d n
  · exact search_bound w hw d n

theorem emit_bound (w : ℕ) (hw : 0<w) (d n i : ℕ) (hi : i<n) :
    CommandsBound (space w d n) (TwoWordGeneralOutputEmit.emitCode w hw d i) := by
  apply append _ _ ?_ (counter_bound w d n 0 d (by omega) _)
  intro cmd hc
  simp only [TwoWordGeneralOutputEmit.putCode,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · change 0<space w d n;unfold space;omega
  · change TwoWordGeneralHistogram.inputBase w d+i<space w d n
    unfold TwoWordGeneralHistogram.inputBase space;omega
  · trivial
  · change 1<space w d n;unfold space;omega

theorem stages_append {w L : ℕ} (a b : List (TwoWordRadixPreparedBuild.Stage (Word w)))
    (ha : BoundedCode L a) (hb : BoundedCode L b) : BoundedCode L (a++b) := by
  intro st hs
  rcases List.mem_append.mp hs with hs | hs
  · exact ha st hs
  · exact hb st hs

theorem output_bound (w : ℕ) (hw : 0<w) (d n start count : ℕ)
    (hc : start+count≤n) :
    BoundedCode (space w d n)
      (TwoWordGeneralPublicUnrolled.outputStages w hw d start count) := by
  induction count generalizing start with
  | zero => intro st hs;simp [TwoWordGeneralPublicUnrolled.outputStages] at hs
  | succ count ih =>
    apply stages_append _ _ (stages_append _ _ (search_stages_bound w hw d n) ?_)
      (ih (start+1) (by omega))
    intro st hs
    simp only [List.mem_singleton] at hs
    subst st
    exact emit_bound w hw d n start (by omega)

theorem code_bound (w : ℕ) (hw : 0<w) (d n : ℕ) :
    BoundedCode (space w d n) (TwoWordGeneralPublicUnrolled.code w hw d n) := by
  apply stages_append _ _ ?_ (output_bound w hw d n 0 n (by omega))
  intro st hs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl
  · exact histogram_bound w hw d n
  · intro cmd hc
    simp only [TwoWordGeneralPublicUnrolled.resetCode,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · trivial
    · change 0<space w d n;unfold space;omega

theorem space_linear (w d n : ℕ) (hn : 2≤n) (hsmall : 2^w≤n) :
    space w d n≤(d+3)*n := by
  have := Nat.mul_le_mul_left d hsmall
  unfold space
  nlinarith

theorem input_base_linear (w d n : ℕ) (hn : 2≤n) (hsmall : 2^w≤n) :
    TwoWordGeneralHistogram.inputBase w d≤(d+2)*n := by
  have := Nat.mul_le_mul_left d hsmall
  unfold TwoWordGeneralHistogram.inputBase
  nlinarith

end CSL.TwoWordGeneralFootprint
end Footprint

section PublicUnrolledComplete
/-!
# Complete actual execution in the public-unrolled Stage model

The input file is the only premise about the initial machine state. Counter
initialization, key reset, searches, decrements, and output writes belong to
the same charged execution. The public, input-length-dependent program
position remains outside the two resident words, as explicitly specified by
`TwoWordGeneralPublicUnrolled`; this is not a uniform charged-control result.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CSL.TwoWordGeneralPublicUnrolled
open TwoWordPhysicalAddresses TwoWordGeneralCounter TwoWordRadixPreparedBuild
open TwoWordGeneralHistogram

theorem output_count (w : ℕ) (xs : List (Word w)) (key : Word w) :
    (output w xs).count key = xs.count key :=
  TwoWordGeneralOutputList.count (fun key => xs.count key) key

theorem output_perm (w : ℕ) (xs : List (Word w)) : (output w xs).Perm xs :=
  TwoWordGeneralOutputList.perm_of_counts (fun key => xs.count key) xs (fun _ => rfl)

theorem output_sorted (w : ℕ) (xs : List (Word w)) : (output w xs).Sorted (· ≤ ·) :=
  TwoWordGeneralOutputList.sorted (fun key => xs.count key)

theorem output_length (w : ℕ) (xs : List (Word w)) : (output w xs).length = xs.length :=
  (output_perm w xs).length_eq

theorem reset_cost (w : ℕ) : transfers (resetCode w) = 1 := rfl

theorem reset_key (w : ℕ) (s : State (Word w)) :
    (execute (resetCode w) s).disk 0 = 0 := by
  simp [resetCode, execute, step]

theorem reset_frame (w : ℕ) (s : State (Word w)) (a : ℕ) (ha : a ≠ 0) :
    (execute (resetCode w) s).disk a = s.disk a := by
  simp [resetCode, execute, step, Function.update_of_ne ha]

theorem reset_value (w d : ℕ) (s : State (Word w)) (key : Word w) :
    value w key 0 d (execute (resetCode w) s).disk = value w key 0 d s.disk := by
  apply value_eq
  intro j hj
  exact reset_frame w s _ (by have := address_large w (0+j) key; omega)

/-- One public program sorts every literal input file from arbitrary scratch.
Multiplicity, the output file, and the I/O bound concern that same execution. -/
theorem complete (w : ℕ) (hw : 0 < w) (d n : ℕ)
    (s : State (Word w)) (xs : List (Word w)) (hlen : xs.length = n)
    (hin : File s.disk (inputBase w d) xs) (hcap : n < (2^w)^d) :
    ∃ t cost, Executes (code w hw d n) s t cost ∧
      cost ≤ budget w d n ∧
      File t.disk (inputBase w d) (output w xs) ∧
      (output w xs).Perm xs ∧ (output w xs).Sorted (· ≤ ·) := by
  subst n
  let hist := execute (histogramCode w hw d xs.length) s
  obtain ⟨hhist, hhistframe⟩ := histogram_correct w hw d s xs hin hcap
  let ready := execute (resetCode w) hist
  have hready : Histogram d ready.disk (output w xs) := by
    intro key
    rw [output_count]
    exact (reset_value w d hist key).trans (hhist key)
  have hkey : ready.disk 0 = 0 := reset_key w hist
  have hcursor : ∀ key ∈ output w xs, ready.disk 0 ≤ key := by
    intro key hmem
    rw [hkey]
    change (0 : Word w).val ≤ key.val
    simp
  obtain ⟨t, outCost, hout, hfile, hframe, hcost⟩ :=
    output_complete w hw d 0 ready (output w xs) hready (output_sorted w xs) hcursor
  have hout' : Executes (outputStages w hw d 0 xs.length) ready t outCost := by
    simpa only [output_length] using hout
  let totalCost := d*2^w + (3+6*d)*xs.length + 1 + outCost
  refine ⟨t, totalCost, ?_, ?_, ?_, output_perm w xs, output_sorted w xs⟩
  · have hreset := Executes.straight (resetCode w) (outputStages w hw d 0 xs.length)
      hist t outCost hout'
    have hrun := Executes.straight (histogramCode w hw d xs.length)
      (.straight (resetCode w) :: outputStages w hw d 0 xs.length) s t
      (transfers (resetCode w) + outCost) hreset
    simpa only [code, List.cons_append, List.nil_append, histogram_cost, reset_cost,
      totalCost, Nat.add_assoc] using hrun
  · have hlast := (t.disk 0).isLt
    rw [hkey, output_length] at hcost
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at hcost
    have hbound : outCost ≤ slope d * (xs.length+2^w) :=
      hcost.trans (Nat.mul_le_mul_left _ (by omega))
    try dsimp only [totalCost, budget, slope] at *
    nlinarith
  · simpa only [Nat.add_zero] using hfile

/-- The narrow-word branch needs only the original constant-word lower
bound. The extra digit is derived, not assumed as successful execution. -/
theorem narrow_complete (w c n : ℕ) (hn : 2 ≤ n)
    (hc : Nat.clog 2 n ≤ c*w) (hsmall : w < Nat.clog 2 n)
    (s : State (Word w)) (xs : List (Word w)) (hlen : xs.length = n)
    (hin : File s.disk (inputBase w (c+1)) xs) :
    ∃ hw : 0 < w, ∃ t cost, Executes (code w hw (c+1) n) s t cost ∧
      cost ≤ 300*(c+2)*n ∧
      File t.disk (inputBase w (c+1)) (output w xs) ∧
      (output w xs).Perm xs ∧ (output w xs).Sorted (· ≤ ·) := by
  have hw := (TwoWordGeneralCapacity.positive_width n w c hn hc).1
  obtain ⟨t, cost, hrun, hcost, hfile, hperm, hsorted⟩ :=
    complete w hw (c+1) n s xs hlen hin
      (TwoWordGeneralCapacity.counter_capacity n w c hw hc)
  refine ⟨hw, t, cost, hrun, ?_, hfile, hperm, hsorted⟩
  have hk := TwoWordGeneralCapacity.alphabet_lt_length n w hsmall
  unfold budget at hcost
  nlinarith

end CSL.TwoWordGeneralPublicUnrolled
end PublicUnrolledComplete


