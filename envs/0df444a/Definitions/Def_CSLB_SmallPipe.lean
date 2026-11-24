-- Prove2me | Definitions.Def_CSLB_SmallPipe
-- name    : CSLB_SmallPipe
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:14:29.676828+00:00
-- url     : https://prove2.me/theorems/edd415b1-f133-4c62-b0a4-b2a636a771db
-- title:
--   Coded sorting bridge: SmallPipe
-- statement:
--   # Expand, sort one word per block, compress: a straight-line machine program
--
--   Given a straight-line two-word program `core` (one word per address) that maps an array of
--   `N` words at addresses `A, …, A+N-1` to the array `ys`, the block program
--   `expand ++ lift core ++ compress` sorts a compact file of `N` words on the external-memory
--   machine: input word `j` is copied to its own block, the lifted core runs on those blocks, and
--   the result is packed back into words `0, …, N-1`.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Definitions.Def_CSLB_StraightBridge

/-! # Expand, sort one word per block, compress: a straight-line machine program

Given a straight-line two-word program `core` (one word per address) that maps an array of
`N` words at addresses `A, …, A+N-1` to the array `ys`, the block program
`expand ++ lift core ++ compress` sorts a compact file of `N` words on the external-memory
machine: input word `j` is copied to its own block, the lifted core runs on those blocks, and
the result is packed back into words `0, …, N-1`. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CSLB.SmallPipe
open CodedSorting CSL CSLB.StraightBridge

variable {M B w : ℕ}

/-- The straight block program. -/
def pipeCode (hB : 0 < B) (N A : ℕ) (core : List (TwoWordPhysicalAddresses.Command (Word w))) :
    List (TwoWordBlockLift.Command B (Word w)) :=
  TwoWordBlockFormat.expand hB (N + A) N ++ core.map (TwoWordBlockLift.compile hB (N + 5)) ++
    TwoWordBlockFormat.compress hB (N + A) N

theorem pipe_bound (hB : 0 < B) (N A Lc : ℕ) (core : List (TwoWordPhysicalAddresses.Command (Word w)))
    (hL : ∀ cmd ∈ core, TwoWordRadixFootprint.BoundedCommand Lc cmd) :
    TwoWordBlockFootprint.BoundedCode (2 * N + A + 5 + Lc) (pipeCode hB N A core) := by
  intro cmd hc
  simp only [pipeCode, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · -- expand
    have key : ∀ n, n ≤ N → ∀ cmd ∈ TwoWordBlockFormat.expand (W := Word w) hB (N + A) n,
        TwoWordBlockFootprint.BoundedCommand (2 * N + A + 5 + Lc) cmd := by
      intro n
      induction n with
      | zero => intro _ cmd h; simp [TwoWordBlockFormat.expand] at h
      | succ n ih =>
        intro hn cmd h
        simp only [TwoWordBlockFormat.expand, List.mem_append] at h
        rcases h with h | h
        · exact ih (by omega) cmd h
        · simp only [TwoWordBlockFormat.expandOne, List.mem_cons, List.not_mem_nil,
            or_false] at h
          rcases h with rfl | rfl | rfl
          · change n / B < _
            have := Nat.div_le_self n B; omega
          · trivial
          · intro _; change N + A + 5 + n < _; omega
    exact key N le_rfl cmd hc
  · obtain ⟨c, hmem, rfl⟩ := List.mem_map.mp hc
    have h := TwoWordBlockFootprint.compile_bound hB (N + 5) Lc c (hL c hmem)
    cases c <;> simp only [TwoWordBlockLift.compile, TwoWordBlockFootprint.BoundedCommand] at h ⊢
    all_goals first | omega | trivial | (intro r; have := h r; omega)
  · have key : ∀ n, n ≤ N → ∀ cmd ∈ TwoWordBlockFormat.compress (W := Word w) hB (N + A) n,
        TwoWordBlockFootprint.BoundedCommand (2 * N + A + 5 + Lc) cmd := by
      intro n
      induction n with
      | zero => intro _ cmd h; simp [TwoWordBlockFormat.compress] at h
      | succ n ih =>
        intro hn cmd h
        simp only [TwoWordBlockFormat.compress, List.mem_append] at h
        rcases h with h | h
        · exact ih (by omega) cmd h
        · simp only [TwoWordBlockFormat.compressOne, List.mem_cons, List.not_mem_nil,
            or_false] at h
          rcases h with rfl | rfl | rfl | rfl
          · change N + A + 5 + n < _; omega
          · intro _; change n / B < _
            have := Nat.div_le_self n B; omega
          · trivial
          · intro _; change n / B < _
            have := Nat.div_le_self n B; omega
    exact key N le_rfl cmd hc

theorem pipe_transfers (hB : 0 < B) (N A : ℕ) (core : List (TwoWordPhysicalAddresses.Command (Word w))) :
    TwoWordBlockLift.transfers (pipeCode hB N A core) =
      5 * N + TwoWordPhysicalAddresses.transfers core := by
  simp only [pipeCode, TwoWordBlockFormat.transfers_append, TwoWordBlockFormat.expand_cost,
    TwoWordBlockFormat.compress_cost, TwoWordBlockLift.transfers_compile]
  omega

/-- Semantics of the straight block program on the two-buffer state. -/
theorem pipe_execute (hB : 0 < B) (N A : ℕ) (core : List (TwoWordPhysicalAddresses.Command (Word w)))
    (xs ys : List (Word w)) (hxs : xs.length = N) (hys : ys.length = N)
    (hcore : ∀ s : TwoWordPhysicalAddresses.State (Word w),
      (∀ j (hj : j < N), s.disk (A + j) = xs[j]'(by omega)) →
      ∀ j (hj : j < N), (TwoWordPhysicalAddresses.execute core s).disk (A + j) = ys[j]'(by omega))
    (s : TwoWordBlockLift.State B (Word w)) (hin : TwoWordBlockFormat.File hB s.disk xs) :
    TwoWordBlockFormat.File hB (TwoWordBlockLift.execute (pipeCode hB N A core) s).disk ys := by
  unfold pipeCode
  rw [TwoWordBlockFormat.execute_append, TwoWordBlockFormat.execute_append]
  set s1 := TwoWordBlockLift.execute (TwoWordBlockFormat.expand hB (N + A) N) s with hs1
  have h1 := TwoWordBlockFormat.expand_correct hB (N + A) N s xs hxs (by omega) hin
  set s2 := TwoWordBlockLift.execute (core.map (TwoWordBlockLift.compile hB (N + 5))) s1 with hs2
  have hobs := TwoWordBlockLift.execute_observe hB (N + 5) core s1
  have h2 : ∀ j : Fin ys.length,
      (TwoWordBlockLift.observe hB (N + A) s2).disk (5 + j.val) = ys.get j := by
    intro j
    have hj : j.val < N := by have := j.isLt; omega
    have hc := hcore (TwoWordBlockLift.observe hB (N + 5) s1) (by
      intro i hi
      have := h1 ⟨i, by omega⟩
      simp only [TwoWordBlockLift.observe] at this ⊢
      rw [show N + 5 + (A + i) = N + A + (5 + i) by omega]
      exact this) j.val hj
    rw [← hobs] at hc
    simp only [TwoWordBlockLift.observe] at hc ⊢
    rw [show N + A + (5 + j.val) = N + 5 + (A + j.val) by omega, hc]
    rfl
  exact TwoWordBlockFormat.compress_correct hB (N + A) N s2 ys hys (by omega) h2

/-- The machine run: halts after `length + 1` steps with the result in words `0, …, N-1`. -/
theorem pipe_run (hB : 0 < B) (hBM : 2 * B ≤ M) (N A Lc : ℕ)
    (core : List (TwoWordPhysicalAddresses.Command (Word w)))
    (hL : ∀ cmd ∈ core, TwoWordRadixFootprint.BoundedCommand Lc cmd)
    (x : Fin N → Word w) (ys : List (Word w)) (hys : ys.length = N)
    (hcore : ∀ s : TwoWordPhysicalAddresses.State (Word w),
      (∀ j (hj : j < N), s.disk (A + j) = x ⟨j, hj⟩) →
      ∀ j (hj : j < N), (TwoWordPhysicalAddresses.execute core s).disk (A + j) = ys[j]'(by omega)) :
    let c := run (program hBM (pipeCode hB N A core)) ((pipeCode hB N A core).length + 1)
      (initCfg x)
    c.halted = true ∧ (∀ j (hj : j < N), c.disk j = ys[j]'(by omega)) ∧
      c.ios = 5 * N + TwoWordPhysicalAddresses.transfers core ∧
      c.maxEnd ≤ (2 * N + A + 5 + Lc) * B := by
  intro c
  set code := pipeCode hB N A core with hcode
  have hL' := pipe_bound hB N A Lc core hL
  obtain ⟨ht, hh, hv, hio, hme⟩ := sim_run hB hBM code _ hL' (initCfg x) rfl rfl code.length le_rfl
  have hc : c = Config.step (program hBM code) (run (program hBM code) code.length (initCfg x)) := by
    simp only [c, run, Function.iterate_succ_apply', hcode]
  obtain ⟨h1, h2, h3, h4⟩ := sim_halt hBM code _ ht hh
  rw [← hc] at h1 h2 h3 h4
  rw [List.take_length] at hv hio
  refine ⟨h1, ?_, ?_, ?_⟩
  · intro j hj
    have hin : TwoWordBlockFormat.File hB (view hBM (initCfg x)).disk (List.ofFn x) := by
      intro i
      have hi : i.val < N := by simpa using i.isLt
      simp only [view, blocks, TwoWordBlockFormat.wordAt, TwoWordBlockFormat.cell, initCfg,
        initCfgOf]
      rw [Nat.div_add_mod']
      simp [inputDisk, hi]
    have hout := pipe_execute hB N A core (List.ofFn x) ys (by simp) hys (by
      intro s hs j hj
      exact hcore s (fun i hi => by rw [hs i hi]; simp) j hj) _ hin
    rw [← hv] at hout
    have := hout ⟨j, by omega⟩
    simp only [view, blocks, TwoWordBlockFormat.wordAt, TwoWordBlockFormat.cell,
      Nat.div_add_mod'] at this
    rw [h2, this]
    rfl
  · rw [h3, hio, pipe_transfers]; simp [initCfg, initCfgOf]
  · rw [h4]; simpa [initCfg, initCfgOf] using hme

end CSLB.SmallPipe


