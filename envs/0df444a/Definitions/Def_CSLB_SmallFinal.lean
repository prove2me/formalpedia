-- Prove2me | Definitions.Def_CSLB_SmallFinal
-- name    : CSLB_SmallFinal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:46:39.530039+00:00
-- url     : https://prove2.me/theorems/60f78555-ce6c-4baf-91e2-b6d202867229
-- title:
--   Coded sorting bridge: SmallFinal
-- statement:
--   # Sorting with any memory `M ≥ 2B` on the external-memory machine
--
--   For every `N ≥ 2`, block size `B ≥ 1`, memory `M ≥ 2B` and word size `w` with
--   `⌈log₂ N⌉ ≤ c·w`, one fixed machine program (two block buffers, straight-line control) sorts
--   every input of `N` words. Wide words (`N ≤ 2^w`) use the one-bit LSD radix sort, narrow words
--   the counting sort with `c + 1` counter digits. The number of block transfers is at most
--   `(9N+4)·w + (40c+70)·N`, and every transfer stays below disk word
--   `((2c+7)·N + 11 + 2^w)·B`.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Definitions.Def_CSLB_SmallCases

/-! # Sorting with any memory `M ≥ 2B` on the external-memory machine

For every `N ≥ 2`, block size `B ≥ 1`, memory `M ≥ 2B` and word size `w` with
`⌈log₂ N⌉ ≤ c·w`, one fixed machine program (two block buffers, straight-line control) sorts
every input of `N` words. Wide words (`N ≤ 2^w`) use the one-bit LSD radix sort, narrow words
the counting sort with `c + 1` counter digits. The number of block transfers is at most
`(9N+4)·w + (40c+70)·N`, and every transfer stays below disk word
`((2c+7)·N + 11 + 2^w)·B`. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CSLB.SmallFinal
open CodedSorting CSL CSLB.StraightBridge CSLB.SmallPipe CSLB.SmallCases

theorem sorted_of_disk {N w : ℕ} (x : Fin N → Word w) (d : Disk w) (ys : List (Word w))
    (hys : ys.length = N) (hd : ∀ j (hj : j < N), d j = ys[j]'(by omega))
    (hperm : ys.Perm (List.ofFn x)) (hsort : ys.Pairwise (fun a b => a.val ≤ b.val)) :
    IsSortedOutput x d := by
  have heq : List.ofFn (fun i : Fin N => d i) = ys := by
    apply List.ext_get (by simp [hys])
    intro j h1 h2
    have hj : j < N := by simpa using h1
    rw [List.get_ofFn]
    exact hd j hj
  unfold IsSortedOutput
  rw [heq]
  exact ⟨hperm, hsort.imp (fun h => h)⟩

theorem small_sort (c N M B w : ℕ) (hN : 2 ≤ N) (hB : 0 < B) (hBM : 2 * B ≤ M)
    (hw : Nat.clog 2 N ≤ c * w) :
    ∃ P : Program M B w, ∀ x : Fin N → Word w, ∃ T,
      (run P T (initCfg x)).halted = true ∧ IsSortedOutput x (run P T (initCfg x)).disk ∧
      (run P T (initCfg x)).ios ≤ (9 * N + 4) * w + (40 * c + 70) * N ∧
      (run P T (initCfg x)).maxEnd ≤ ((2 * c + 7) * N + 11 + 2 ^ w) * B := by
  have hpos := TwoWordGeneralCapacity.positive_width N w c hN hw
  have hw0 : 0 < w := hpos.1
  by_cases hwide : N ≤ 2 ^ w
  · -- wide words: radix sort
    let core := CSLB.WideRadix.sortCode w hw0 N w
    refine ⟨program hBM (pipeCode hB N 3 core), fun x => ?_⟩
    have hrun := pipe_run hB hBM N 3 (3 + 2 * N + 2 ^ w) core
      (wide_bound w hw0 N w) x (CSLB.WideRadix.radixList w (List.ofFn x))
      (by rw [CSLB.WideRadix.radixList_length]; simp)
      (by
        intro s hs j hj
        exact wide_correct w hw0 N hwide (List.ofFn x) (by simp) s
          (fun i hi => by rw [hs i hi]; simp) j hj)
    obtain ⟨hh, hd, hio, hme⟩ := hrun
    refine ⟨_, hh, ?_, ?_, ?_⟩
    · exact sorted_of_disk x _ _ (by rw [CSLB.WideRadix.radixList_length]; simp) hd
        (CSLB.WideRadix.radixList_perm w _) (CSLB.WideRadix.radixList_sorted _)
    · rw [hio, wide_cost]
      nlinarith
    · refine hme.trans (Nat.mul_le_mul_right _ ?_)
      nlinarith
  · -- narrow words: counting sort
    have hsmall : 2 ^ w < N := by omega
    let d := c + 1
    have hcap : N < (2 ^ w) ^ d := TwoWordGeneralCapacity.counter_capacity_of_covers N w c hN hw
    let core := narrowCode w hw0 d N
    refine ⟨program hBM (pipeCode hB N (TwoWordGeneralHistogram.inputBase w d) core),
      fun x => ?_⟩
    have hrun := pipe_run hB hBM N (TwoWordGeneralHistogram.inputBase w d)
      (3 + d * 2 ^ w + N + 2 ^ w) core
      (narrow_bound w hw0 d N) x (TwoWordGeneralPublicUnrolled.output w (List.ofFn x))
      (by rw [TwoWordGeneralPublicUnrolled.output_length]; simp)
      (by
        intro s hs j hj
        exact narrow_correct w hw0 d N (List.ofFn x) (by simp) hcap s
          (fun i hi => by rw [hs i hi]; simp) j hj)
    obtain ⟨hh, hd, hio, hme⟩ := hrun
    refine ⟨_, hh, ?_, ?_, ?_⟩
    · exact sorted_of_disk x _ _ (by rw [TwoWordGeneralPublicUnrolled.output_length]; simp) hd
        (TwoWordGeneralPublicUnrolled.output_perm w _)
        (TwoWordGeneralPublicUnrolled.output_sorted w _)
    · rw [hio, narrow_cost]
      have h1 : N + 2 ^ w - 1 ≤ 2 * N := by omega
      have h2 : (12 * d + 10) * (N + 2 ^ w - 1) ≤ (12 * d + 10) * (2 * N) :=
        Nat.mul_le_mul_left _ h1
      have h3 : d * 2 ^ w ≤ d * N := Nat.mul_le_mul_left _ hsmall.le
      have h4 : 0 ≤ (9 * N + 4) * w := Nat.zero_le _
      simp only [d] at h2 h3 ⊢
      nlinarith
    · refine hme.trans (Nat.mul_le_mul_right _ ?_)
      have h3 : d * 2 ^ w ≤ d * N := Nat.mul_le_mul_left _ hsmall.le
      unfold TwoWordGeneralHistogram.inputBase
      simp only [d] at h3 ⊢
      nlinarith

end CSLB.SmallFinal


