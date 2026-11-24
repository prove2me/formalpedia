-- Prove2me | Definitions.Def_CSLB_SmallCases
-- name    : CSLB_SmallCases
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:30:58.092828+00:00
-- url     : https://prove2.me/theorems/069500e7-1d44-4262-8e7e-e84c83649c5e
-- title:
--   Coded sorting bridge: SmallCases
-- statement:
--   # The two straight-line one-word sorters used below the memory threshold
--
--   * wide words (`N ≤ 2^w`): the one-bit LSD radix sort of `CSLB.WideRadix`, array at address `3`;
--   * narrow words: counting sort — the histogram of `TwoWordGeneralHistogram`, a reset of the key
--     cell, and the fixed-schedule output of `CSLB.NarrowSlots`, array at `inputBase w d`.
--
--   Both are given as `SmallPipe` cores: correctness on an arbitrary state holding the input array,
--   their transfer counts, and a bound on every address they touch.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Definitions.Def_CSLB_SmallPipe
import Definitions.Def_CSLB_NarrowSlots
import Definitions.Def_CSLB_WideRadix

/-! # The two straight-line one-word sorters used below the memory threshold

* wide words (`N ≤ 2^w`): the one-bit LSD radix sort of `CSLB.WideRadix`, array at address `3`;
* narrow words: counting sort — the histogram of `TwoWordGeneralHistogram`, a reset of the key
  cell, and the fixed-schedule output of `CSLB.NarrowSlots`, array at `inputBase w d`.

Both are given as `SmallPipe` cores: correctness on an arbitrary state holding the input array,
their transfer counts, and a bound on every address they touch. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CSLB.SmallCases
open CSL CSL.TwoWordPhysicalAddresses CSL.TwoWordGeneralCounter

theorem bounded_mono {W : Type*} {L L' : ℕ} (h : L ≤ L') (cmd : Command W)
    (hc : TwoWordRadixFootprint.BoundedCommand L cmd) :
    TwoWordRadixFootprint.BoundedCommand L' cmd := by
  cases cmd <;> simp only [TwoWordRadixFootprint.BoundedCommand] at hc ⊢
  all_goals first | omega | trivial | (intro r; have := hc r; omega)

theorem bounded_append {W : Type*} {L : ℕ} (a b : List (Command W))
    (ha : ∀ c ∈ a, TwoWordRadixFootprint.BoundedCommand L c)
    (hb : ∀ c ∈ b, TwoWordRadixFootprint.BoundedCommand L c) :
    ∀ c ∈ a ++ b, TwoWordRadixFootprint.BoundedCommand L c := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact ha c h
  · exact hb c h

section Wide
open CSLB.WideRadix
variable (w : ℕ) (hw : 0 < w) (n : ℕ)

theorem wide_bound (b : ℕ) :
    ∀ c ∈ sortCode w hw n b, TwoWordRadixFootprint.BoundedCommand (3 + 2 * n + 2 ^ w) c := by
  have hcur : ∀ (bb : ℕ) (x : Word w), cur w bb x < 3 := by
    intro bb x; unfold cur; split <;> omega
  have hcount : ∀ bb i, i ≤ n → ∀ c ∈ countLoop w hw bb i,
      TwoWordRadixFootprint.BoundedCommand (3 + 2 * n + 2 ^ w) c := by
    intro bb i
    induction i with
    | zero => intro _ c h; simp [countLoop] at h
    | succ i ih =>
      intro hi
      apply bounded_append _ _ (ih (by omega))
      intro c h
      simp only [countOne, List.mem_cons, List.not_mem_nil, or_false] at h
      have : 0 < 2 ^ w := by positivity
      rcases h with rfl | rfl | rfl | rfl
      · change 3 + i < _; have := Nat.one_le_two_pow (n := w); omega
      · change 0 < _; have := Nat.one_le_two_pow (n := w); omega
      · trivial
      · intro _; change 0 < _; have := Nat.one_le_two_pow (n := w); omega
  have hscat : ∀ bb i, i ≤ n → ∀ c ∈ scatterLoop w hw n bb i,
      TwoWordRadixFootprint.BoundedCommand (3 + 2 * n + 2 ^ w) c := by
    intro bb i
    induction i with
    | zero => intro _ c h; simp [scatterLoop] at h
    | succ i ih =>
      intro hi
      apply bounded_append _ _ (ih (by omega))
      intro c h
      simp only [scatterOne, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · change 3 + i < _; have := Nat.one_le_two_pow (n := w); omega
      · intro r; change cur w bb r.1 < _; have := hcur bb r.1; have := Nat.one_le_two_pow (n := w); omega
      · trivial
      · intro r; change 3 + n + r.1.val < _; have := r.1.isLt; have := Nat.one_le_two_pow (n := w); omega
      · trivial
      · intro r; change cur w bb r.1 < _; have := hcur bb r.1; have := Nat.one_le_two_pow (n := w); omega
  have hcopy : ∀ i, i ≤ n → ∀ c ∈ copyLoop w n i,
      TwoWordRadixFootprint.BoundedCommand (3 + 2 * n + 2 ^ w) c := by
    intro i
    induction i with
    | zero => intro _ c h; simp [copyLoop] at h
    | succ i ih =>
      intro hi
      apply bounded_append _ _ (ih (by omega))
      intro c h
      simp only [copyOne, List.mem_cons, List.not_mem_nil, or_false] at h
      have : 0 < 2 ^ w := by positivity
      rcases h with rfl | rfl
      · change 3 + n + i < _; have := Nat.one_le_two_pow (n := w); omega
      · intro _; change 3 + i < _; have := Nat.one_le_two_pow (n := w); omega
  induction b with
  | zero => intro c h; simp [sortCode] at h
  | succ b ih =>
    apply bounded_append _ _ ih
    have : 0 < 2 ^ w := by positivity
    unfold passCode
    refine bounded_append _ _ (bounded_append _ _ (bounded_append _ _ (bounded_append _ _ ?_
      (hcount b n le_rfl)) ?_) (hscat b n le_rfl)) (hcopy n le_rfl)
    · intro c h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · trivial
      · intro _; change 0 < _; have := Nat.one_le_two_pow (n := w); omega
    · intro c h
      simp only [initCode, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · change 0 < _; have := Nat.one_le_two_pow (n := w); omega
      · intro _; change 2 < _; have := Nat.one_le_two_pow (n := w); omega
      · trivial
      · intro _; change 1 < _; have := Nat.one_le_two_pow (n := w); omega

theorem wide_correct (hcap : n ≤ 2 ^ w) (xs : List (Word w)) (hlen : xs.length = n)
    (s : State (Word w)) (hin : ∀ j (hj : j < n), s.disk (3 + j) = xs[j]'(by omega)) :
    ∀ j (hj : j < n), (execute (sortCode w hw n w) s).disk (3 + j) =
      (radixList w xs)[j]'(by rw [radixList_length]; omega) := by
  have h := sort_correct w hw n xs hlen hcap s (fun i hi => hin i (by omega)) w
  intro j hj
  exact h j (by rw [radixList_length]; omega)

theorem wide_cost : transfers (sortCode w hw n w) = (9 * n + 4) * w := sortCode_cost w hw n w

end Wide

section Narrow
open CSL.TwoWordGeneralHistogram CSL.TwoWordGeneralCounter
variable (w : ℕ) (hw : 0 < w) (d : ℕ)

/-- The narrow-word counting sort on `n` words. -/
def narrowCode (n : ℕ) : List (Command (Word w)) :=
  histogramCode w hw d n ++ TwoWordGeneralPublicUnrolled.resetCode w ++
    NarrowSlots.outputCode w hw d (n + 2 ^ w - 1)

theorem value_update0 (key : Word w) (v : Word w) (count : ℕ) :
    ∀ (start : ℕ) (disk : ℕ → Word w),
      TwoWordGeneralCounter.value w key start count (Function.update disk 0 v) =
        TwoWordGeneralCounter.value w key start count disk := by
  induction count with
  | zero => intro _ _; rfl
  | succ count ih =>
    intro start disk
    simp only [TwoWordGeneralCounter.value, ih]
    rw [Function.update_of_ne]
    have := TwoWordGeneralCounter.address_large w start key
    omega

theorem narrow_correct (n : ℕ) (xs : List (Word w)) (hlen : xs.length = n)
    (hcap : n < (2 ^ w) ^ d)
    (s : State (Word w)) (hin : ∀ j (hj : j < n), s.disk (inputBase w d + j) = xs[j]'(by omega)) :
    ∀ j (hj : j < n), (execute (narrowCode w hw d n) s).disk (inputBase w d + j) =
      (TwoWordGeneralPublicUnrolled.output w xs)[j]'(by
        rw [TwoWordGeneralPublicUnrolled.output_length]; omega) := by
  have hfile : TwoWordGeneralHistogram.File s.disk (inputBase w d) xs :=
    fun i hi => hin i (by omega)
  obtain ⟨hhist, _⟩ := histogram_correct w hw d s xs hfile (by omega)
  subst hlen
  set s1 := execute (histogramCode w hw d xs.length) s
  set s2 := execute (TwoWordGeneralPublicUnrolled.resetCode w) s1 with hs2
  have hd2 : s2.disk = Function.update s1.disk 0 0 := rfl
  have hhist2 : Histogram d s2.disk (TwoWordGeneralPublicUnrolled.output w xs) := by
    intro key
    rw [hd2]
    change TwoWordGeneralCounter.value w key 0 d (Function.update s1.disk 0 0) = _
    rw [value_update0]
    rw [(TwoWordGeneralPublicUnrolled.output_perm w xs).count_eq]
    exact hhist key
  have hkey : s2.disk 0 = 0 := by rw [hd2]; simp
  have hout := NarrowSlots.output_correct w hw d s2 xs hhist2 hkey
  intro j hj
  unfold narrowCode
  rw [TwoWordGeneralCounter.execute_append, TwoWordGeneralCounter.execute_append]
  exact hout j (by rw [TwoWordGeneralPublicUnrolled.output_length]; omega)

theorem narrow_bound (n : ℕ) :
    ∀ c ∈ narrowCode w hw d n,
      TwoWordRadixFootprint.BoundedCommand (3 + d * 2 ^ w + n + 2 ^ w) c := by
  have hmono : ∀ (code : List (Command (Word w))),
      TwoWordGeneralFootprint.CommandsBound (TwoWordGeneralFootprint.space w d n) code →
      ∀ c ∈ code, TwoWordRadixFootprint.BoundedCommand (3 + d * 2 ^ w + n + 2 ^ w) c := by
    intro code h c hc
    exact bounded_mono (by unfold TwoWordGeneralFootprint.space; have := Nat.one_le_two_pow (n := w); omega) c (h c hc)
  have hslots : ∀ S, S ≤ n + 2 ^ w - 1 → ∀ c ∈ NarrowSlots.outputCode w hw d S,
      TwoWordRadixFootprint.BoundedCommand (3 + d * 2 ^ w + n + 2 ^ w) c := by
    intro S
    induction S with
    | zero => intro _ c h; simp [NarrowSlots.outputCode] at h
    | succ S ih =>
      intro hS
      apply bounded_append _ _ (ih (by omega))
      unfold NarrowSlots.slotCode
      have h2 : 0 < 2 ^ w := by positivity
      refine bounded_append _ _ (bounded_append _ _ (bounded_append _ _ (bounded_append _ _
        (hmono _ (TwoWordGeneralFootprint.test_bound w hw d n)) ?_) ?_)
        (hmono _ (TwoWordGeneralFootprint.counter_bound w d n 0 d (by omega) _))) ?_
      · intro c h
        simp only [NarrowSlots.putCode, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · change 0 < _; have := Nat.one_le_two_pow (n := w); omega
        · intro r; change inputBase w d + (S - r.2.val) < _
          unfold inputBase; have := Nat.one_le_two_pow (n := w); omega
      · intro c h
        simp only [NarrowSlots.borrowCode, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · change TwoWordGeneralOutput.flagAddress w d < _
          unfold TwoWordGeneralOutput.flagAddress; have := Nat.one_le_two_pow (n := w); omega
        · change 1 < _; have := Nat.one_le_two_pow (n := w); omega
      · intro c h
        simp only [NarrowSlots.advanceCode, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl
        · change TwoWordGeneralOutput.flagAddress w d < _
          unfold TwoWordGeneralOutput.flagAddress; have := Nat.one_le_two_pow (n := w); omega
        · change 0 < _; have := Nat.one_le_two_pow (n := w); omega
        · trivial
        · intro _; change 0 < _; have := Nat.one_le_two_pow (n := w); omega
  unfold narrowCode
  refine bounded_append _ _ (bounded_append _ _
    (hmono _ (TwoWordGeneralFootprint.histogram_bound w hw d n)) ?_) (hslots _ le_rfl)
  intro c h
  simp only [TwoWordGeneralPublicUnrolled.resetCode, List.mem_cons, List.not_mem_nil,
    or_false] at h
  have h2 : 0 < 2 ^ w := by positivity
  rcases h with rfl | rfl
  · trivial
  · change 0 < _; have := Nat.one_le_two_pow (n := w); omega

theorem narrow_cost (n : ℕ) :
    transfers (narrowCode w hw d n) =
      d * 2 ^ w + (3 + 6 * d) * n + 1 + (12 * d + 10) * (n + 2 ^ w - 1) := by
  unfold narrowCode
  rw [TwoWordGeneralCounter.transfers_append, TwoWordGeneralCounter.transfers_append,
    histogram_cost, NarrowSlots.outputCode_cost]
  rfl

end Narrow

end CSLB.SmallCases


