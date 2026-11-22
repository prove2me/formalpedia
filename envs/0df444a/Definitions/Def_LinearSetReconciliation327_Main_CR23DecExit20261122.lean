-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CR23DecExit20261122
-- name    : LinearSetReconciliation327_Main_CR23DecExit20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:58:31.167494+00:00
-- url     : https://prove2.me/theorems/1b21e6ef-2d18-418c-a068-f7f076631d24
-- title:
--   Proposition 2.3's decoder, with the exit register `r0 = decOutBase N t`
-- statement:
--   The publishable form of Proposition 2.3's run with one added conjunct: the emit postlude leaves `s'.regs 0 = decOutBase N t`, i.e. the address of the decoded output window.  `decStmt_halts_exit` states that from `decoderStart W (cr23Sketch N t C x) []` the decoder halts within `decStmtCost N t + 1` steps with `OutputsSupport s' x` *and* `s'.regs 0 = decOutBase N t`.  This is what a reader of the output window needs: the CR stage's merge consumes the decoded residual through `(regs 0, regs 1)`, and no published statement exposed those registers.  `decEmitStmt_spec_exit` and `decStmt_sem_exit` are the accepted `decEmitStmt_spec`/`decStmt_sem` with the conjunct threaded through the `Sem.seq`/`Sem.mono` plumbing.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's `cr` stage and Proposition 2.3.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23DecRun20261122

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

/-! ## The decoder's exit registers -/

theorem decEmitStmt_spec_exit (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x z : Fin N → ZMod 2)
    (w tag : ℕ) (P : Finset ℕ) (mst : List ℕ) (st : RAMState) (Pgm : Program) (a : ℕ)
    (hAt : At Pgm a (Stmt.compile decEmitStmt a))
    (hpc : st.pc = a) (hw : w = 0)
    (hH : DecHead1 N t C x z w tag P mst st) (hK : cr23Supp z = ∅) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) a (a + decEmitStmt.len) st
      (fun k s' => k ≤ decEmitStmtCost N t ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) := by
  subst hw
  obtain ⟨hHead, hmstN, hpar1⟩ := hH
  obtain ⟨hD, h14, hP', hsub, hcap0, hcard⟩ := hHead
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h11s, h12s, h13s, h14s, -, -, hpar, hmst⟩ := hD
  have hcap : mst.length ≤ 2 * t + 1 := by
    have h := hcap0
    omega
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  have hEW : E.W = cr23Word N := rfl
  have hpar0 := decPar_if_eq N t P st hpar1 hpar
  have hbel : ∀ b, b < decParBase N t → st.mem b = st.mem b := fun _ _ => rfl
  have hsl11 : st.mem (decSlot N t 11) = decMstBase N t := h11s
  have hsl12 : st.mem (decSlot N t 12) = decParBase N t := h12s
  have hsl13 : st.mem (decSlot N t 13) = decOutBase N t := h13s
  have hsl14 : st.mem (decSlot N t 14) = mst.length := h14s
  -- split the compile: init · (loop · post)
  have hAtAll : At Pgm a (decEmitInit ++ (Stmt.compile
      (Stmt.loop (Cond.lt r13 r0 r2) (Stmt.code decEmitBody)) (a + decEmitInit.length)
        ++ decEmitPost)) := hAt
  obtain ⟨hAtI, hAtAll⟩ := At.append.mp hAtAll
  obtain ⟨hAtL0, hAtP0⟩ := At.append.mp hAtAll
  have hlooplen : (Stmt.compile (Stmt.loop (Cond.lt r13 r0 r2) (Stmt.code decEmitBody))
      (a + decEmitInit.length)).length = 12 := by
    rw [Stmt.length_compile]
    simp only [Stmt.len, Cond.code, decEmitBody_len, List.length_cons, List.length_nil]
  have hAtPost : At Pgm (a + decEmitInit.length + 12) decEmitPost := by
    have h := hAtP0
    rw [hlooplen] at h
    exact h
  -- the initialisation
  have hInitInv : DecEmitInv N t P mst 0 0 [] st.mem (runBlock decEmitInit E st) :=
    decEmitInit_data N t hN htN E hEW P mst st.mem st h14 hbel hsl11 hsl12 hsl13 hsl14 hcap hpar0
  have hInitPc : (runBlock decEmitInit E st).pc = a + decEmitInit.length := by
    rw [runBlock_pc decEmitInit E st decEmitInit_noBranch, hpc]
  -- the walk
  have hLoop := decEmit_loop N t hN htN E hEW P mst st.mem Pgm (a + decEmitInit.length) hAtL0
    hcap hmstN hmst (runBlock decEmitInit E st) hInitPc hInitInv
  have hLoopP : Sem Pgm E (a + decEmitInit.length) (a + decEmitInit.length + 12)
      (runBlock decEmitInit E st)
      (fun k s' => k ≤ 2 + 12 * mst.length ∧
        (∃ cnt lacc, DecEmitInv N t P mst mst.length cnt lacc st.mem s') ∧
        s'.pc = a + decEmitInit.length + 12) :=
    Sem.mono hLoop (fun k s' h => ⟨h.1, h.2.1, h.2.2⟩)
  -- the postlude
  have hOutW : decOutBase N t < 2 ^ E.W := by
    rw [hEW]; exact dec_out_add_lt_word N t hN htN (j := 0) (by omega)
  have hPostSem : ∀ (s1 : RAMState),
      (∃ cnt lacc, DecEmitInv N t P mst mst.length cnt lacc st.mem s1) →
      s1.pc = a + decEmitInit.length + 12 →
      Sem Pgm E (a + decEmitInit.length + 12)
        (a + decEmitInit.length + 12 + decEmitPost.length) s1
        (fun k s' => k = decEmitPost.length ∧ s'.regs r0 = decOutBase N t ∧
          s'.mem = s1.mem ∧ s'.regs r1 = s1.regs r1) := by
    intro s1 hInv1 hpc1
    obtain ⟨cnt, lacc, hI1⟩ := hInv1
    obtain ⟨-, -, -, -, -, -, h10, -, -, -, -, -, -, -, -, -⟩ := hI1
    refine Sem.mono (Sem.block Pgm E (a + decEmitInit.length + 12) decEmitPost s1 hAtPost
      decEmitPost_noBranch hpc1) ?_
    rintro k s' ⟨hk, rfl⟩
    exact ⟨hk, decEmitPost_spec E s1 (decOutBase N t) h10 hOutW,
      decEmitPost_mem E s1, decEmitPost_frame E s1 r1 (by decide)⟩
  -- init · (loop · post)
  refine Sem.mono (Sem.seq
    (Q₁ := fun k0 s0 => k0 = decEmitInit.length ∧ s0 = runBlock decEmitInit E st)
    (Q₂ := fun k0 k' s' => ∃ k1 k2, k' = k1 + k2 ∧ k0 = decEmitInit.length ∧
      k1 ≤ 2 + 12 * mst.length ∧ k2 = decEmitPost.length ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t)
    (Sem.block Pgm E a decEmitInit st hAtI decEmitInit_noBranch hpc) ?_) ?_
  · intro k0 s0 hQ0
    obtain ⟨hk0, rfl⟩ := hQ0
    refine Sem.seq
      (Q₁ := fun k1 s1 => k1 ≤ 2 + 12 * mst.length ∧
        (∃ cnt lacc, DecEmitInv N t P mst mst.length cnt lacc st.mem s1) ∧
        s1.pc = a + decEmitInit.length + 12)
      (Q₂ := fun k1 k2 s' => k0 = decEmitInit.length ∧ k1 ≤ 2 + 12 * mst.length ∧
        k2 = decEmitPost.length ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) hLoopP ?_
    intro k1 s1 hQ1
    obtain ⟨hk1, hInv1, hpc1⟩ := hQ1
    refine Sem.mono (hPostSem s1 hInv1 hpc1) (fun k s' hh => ⟨hk0, hk1, hh.1, ?_, hh.2.1⟩)
    exact decEmit_outputsSupport_post N t P mst st.mem s1 s' x z hP' hK hsub
      hh.2.1 hh.2.2.1 hh.2.2.2 hInv1
  · rintro k s' ⟨k0, k', hk, k1, k2, hk', h16, hk1, hk2, hout, hr0⟩
    refine ⟨?_, hout, hr0⟩
    have hle := decEmitStmtCost_le N t mst hcap
    omega

theorem decStmt_sem_exit (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t)
    (Pgm : Program) (hAt : At Pgm 0 (Stmt.compile decStmt 0))
    (st : RAMState) (hpc : st.pc = 0) (h0 : st.regs r0 = 0)
    (hpay : ∀ a, a < wordsOf (cr23Word N) (cr23R N t) →
      st.mem a = packMem (cr23Word N) (cr23Sketch N t C x) a)
    (hzero : ∀ a, wordsOf (cr23Word N) (cr23R N t) ≤ a → st.mem a = 0) :
    Sem Pgm (detEnv (cr23Word N) (cr23DecDet N t C)) 0 decStmt.len st
      (fun k s' => k ≤ decStmtCost N t ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) := by
  set E : RAMEnv := detEnv (cr23Word N) (cr23DecDet N t C) with hE
  set n : ℕ := Nat.clog 4 (t + 1) with hn
  -- the compile, peeled one `Stmt.compile` step at a time
  have h1 : At Pgm 0 (Stmt.compile decStmt 0) := hAt
  rw [decStmt_eq1] at h1
  obtain ⟨hAtC0, h1⟩ := At.append.mp h1
  simp only [Stmt.length_compile, Stmt.len, progDecPreC_len, Nat.zero_add] at h1
  obtain ⟨hAtS0, h1⟩ := At.append.mp h1
  simp only [Stmt.length_compile, Stmt.len, progDecPreS_len, Nat.zero_add] at h1
  obtain ⟨hAtL0, h1⟩ := At.append.mp h1
  simp only [Stmt.length_compile, Stmt.len, decLoadW_len, Nat.zero_add] at h1
  obtain ⟨hAtR, hAtE0⟩ := At.append.mp h1
  have hAtC : At Pgm 0 progDecPreC := hAtC0
  have hAtS : At Pgm 22 progDecPreS := hAtS0
  have hAtL63 : At Pgm 63 decLoadW := hAtL0
  have hAtPre : At Pgm 0 progDecPre := by
    rw [progDecPre]
    exact At.append.mpr ⟨hAtC, hAtS⟩
  have hpre : progDecPre.length = 63 := progDecPre_len
  have hAtE : At Pgm (66 + decRoundBody.len + 2)
      (Stmt.compile decEmitStmt (66 + decRoundBody.len + 2)) := by
    have h := hAtE0
    simp only [Stmt.length_compile, decRoundStmt_len_form, Nat.zero_add] at h
    exact h
  have hW1 : 1 < 2 ^ E.W := by rw [hE]; exact cr23_one_lt_word N hN
  have hF8 : cr23DecFrame N t + 8 < 2 ^ E.W := by
    rw [hE]; exact dec_frame_add_lt_word N t hN htN (by norm_num)
  have htW : t < 2 ^ E.W := by
    rw [hE]; exact lt_of_le_of_lt htN (cr23N_lt_word N hN)
  -- leg 1: the prologue
  have hProl : Sem Pgm E 0 63 st
      (fun k s' => (k = 63 ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r14 = cr23DecFrame N t) ∧ s'.pc = 63) := by
    have h := decPrologue_spec N t hN htN C x hsup Pgm hAtPre st hpc h0 hpay hzero
    rw [hpre] at h
    exact Sem.add_pc h
  -- leg 2: the counter reload
  have hL2 : ∀ (s1 : RAMState), s1.pc = 63 → DecHead1 N t C x x t 1 ∅ [] s1 →
      s1.regs r14 = cr23DecFrame N t →
      Sem Pgm E 63 66 s1
        (fun k s' => k = decLoadW.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
          s'.regs r9 = t ∧ s'.pc = 66) := by
    intro s1 hpc1 hH1 h141
    have hblk := Sem.block Pgm E 63 decLoadW s1 hAtL63 decLoadW_noBranch hpc1
    have hspec := decLoadW_spec E s1 (cr23DecFrame N t) hW1 h141 hF8
    obtain ⟨h9, hmem, hpc3, hframe⟩ := hspec
    have h7 : s1.mem (cr23DecFrame N t + 8) = t := by
      obtain ⟨hD0, -, -⟩ := hH1
      obtain ⟨hD1, -, -, -, -, -⟩ := hD0
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
        a19⟩ := hD1
      have h := a8
      rwa [decSlot_seven] at h
    have h9' : (runBlock decLoadW E s1).regs r9 = t := by
      rw [h9, h7, Nat.mod_eq_of_lt htW]
    have hH1' : DecHead1 N t C x x t 1 ∅ [] (runBlock decLoadW E s1) :=
      DecHead1_congr hmem.symm (hframe r14 (by decide) (by decide)).symm hH1
    refine Sem.mono hblk (fun k s' hh => ?_)
    obtain ⟨hk, rfl⟩ := hh
    exact ⟨hk, hH1', h9', by rw [hpc3, hpc1]⟩
  -- leg 3: the round loop
  have hL3 : ∀ (s2 : RAMState), s2.pc = 66 → DecHead1 N t C x x t 1 ∅ [] s2 →
      s2.regs r9 = t →
      Sem Pgm E 66 (66 + decRoundBody.len + 2) s2
        (fun k s' => k ≤ 1 + n * (decRoundCost N t + 2) ∧
          DecLoopInv N t C x n s' ∧ s'.pc = (66 + decRoundBody.len + 2)) := by
    intro s2 hpc2 hH2 h92
    exact decRoundStmt_spec N t hN ht htN C x eps hexp heps Pgm 66 hAtR s2 hpc2 hH2 h92
  -- leg 4: the emit pass
  have hw0 : t / 4 ^ n = 0 := by
    rw [hn]
    refine Nat.div_eq_of_lt ?_
    have h := Nat.le_pow_clog (b := 4) (by norm_num : 1 < 4) (t + 1)
    omega
  have hL4 : ∀ (s3 : RAMState), s3.pc = (66 + decRoundBody.len + 2) →
      DecLoopInv N t C x n s3 →
      Sem Pgm E (66 + decRoundBody.len + 2)
        (66 + decRoundBody.len + 2 + decEmitStmt.len) s3
        (fun k s' => k ≤ decEmitStmtCost N t ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) := by
    intro s3 hpc3 hInv
    obtain ⟨z, P, mst, hH3, -⟩ := hInv
    rw [hw0] at hH3
    have hH3' := hH3
    obtain ⟨⟨-, -, -, -, -, hwc⟩, -, -⟩ := hH3'
    have hK : cr23Supp z = ∅ := Finset.card_eq_zero.mp (by omega)
    exact decEmitStmt_spec_exit N t hN htN C x z 0 (1 + n) P mst s3 Pgm (66 + decRoundBody.len + 2)
      hAtE hpc3 rfl hH3 hK
  -- 1 · 2
  have h12 : Sem Pgm E 0 66 st
      (fun k s' => k = 63 + decLoadW.length ∧ DecHead1 N t C x x t 1 ∅ [] s' ∧
        s'.regs r9 = t ∧ s'.pc = 66) := by
    refine Sem.mono (Sem.seq (Q₁ := fun k1 s1 => (k1 = 63 ∧ DecHead1 N t C x x t 1 ∅ [] s1 ∧
        s1.regs r14 = cr23DecFrame N t) ∧ s1.pc = 63)
      (Q₂ := fun k1 k2 s' => k1 = 63 ∧ k2 = decLoadW.length ∧
        DecHead1 N t C x x t 1 ∅ [] s' ∧ s'.regs r9 = t ∧ s'.pc = 66) hProl ?_) ?_
    · intro k1 s1 hQ1
      obtain ⟨⟨hk1, hH1, h141⟩, hpc1⟩ := hQ1
      exact Sem.mono (hL2 s1 hpc1 hH1 h141)
        (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2⟩)
    · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4, h5⟩
      exact ⟨by omega, h3, h4, h5⟩
  -- (1 · 2) · 3
  have h123 : Sem Pgm E 0 (66 + decRoundBody.len + 2) st
      (fun k s' => k ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
        DecLoopInv N t C x n s' ∧ s'.pc = (66 + decRoundBody.len + 2)) := by
    refine Sem.mono (Sem.seq (Q₁ := fun k1 s1 => k1 = 63 + decLoadW.length ∧
        DecHead1 N t C x x t 1 ∅ [] s1 ∧ s1.regs r9 = t ∧ s1.pc = 66)
      (Q₂ := fun k1 k2 s' => k1 = 63 + decLoadW.length ∧
        k2 ≤ 1 + n * (decRoundCost N t + 2) ∧ DecLoopInv N t C x n s' ∧
        s'.pc = (66 + decRoundBody.len + 2)) h12 ?_) ?_
    · intro k1 s1 hQ1
      obtain ⟨hk1, hH1, h91, hpc1⟩ := hQ1
      exact Sem.mono (hL3 s1 hpc1 hH1 h91)
        (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2⟩)
    · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4⟩
      exact ⟨by omega, h3, h4⟩
  -- everything
  have htotal : (66 + decRoundBody.len + 2 + decEmitStmt.len) = decStmt.len := by
    rw [decStmt_len_form, progDecPreC_len, progDecPreS_len, decLoadW_len, decRoundStmt_len_form,
      decEmitStmt_len_form]
    omega
  refine Sem.end_congr (Sem.mono (Sem.seq
    (Q₁ := fun k1 s1 => k1 ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
      DecLoopInv N t C x n s1 ∧ s1.pc = (66 + decRoundBody.len + 2))
    (Q₂ := fun k1 k2 s' => k1 ≤ 63 + decLoadW.length + (1 + n * (decRoundCost N t + 2)) ∧
      k2 ≤ decEmitStmtCost N t ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) h123 ?_) ?_) htotal
  · intro k1 s1 hQ1
    obtain ⟨hk1, hInv1, hpc1⟩ := hQ1
    exact Sem.mono (hL4 s1 hpc1 hInv1) (fun k s' hh => ⟨hk1, hh.1, hh.2.1, hh.2.2⟩)
  · rintro k s' ⟨k1, k2, hk, h1, h2, h3, h4⟩
    refine ⟨?_, h3, h4⟩
    have hle := decStmtCost_le N t k1 k2 h1 h2
    omega
/-- **The decoder's publishable form, with the exit register.**  Same run as
`cr23_decoding`, plus the fact that the emit postlude leaves `r0 = decOutBase N t`
(which is what a reader of the output window needs). -/
theorem decStmt_halts_exit (N t : ℕ) (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (x : Fin N → ZMod 2) (eps : ℝ)
    (hexp : IsLayeredExpander C (2 * t) eps) (heps : 16 * eps ≤ 1)
    (hsup : (cr23Supp x).card ≤ t) :
    ∃ s' : RAMState,
      HaltsWithin progDec (detEnv (cr23Word N) (cr23DecDet N t C))
        ((decStmtCost N t : ℝ) + 1)
        (decoderStart (cr23Word N) (cr23Sketch N t C x) []) s' ∧
        OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t := by
  have hsem := decStmt_sem_exit N t hN ht htN C x eps hexp heps hsup progDec progDec_at_main
    (decoderStart (cr23Word N) (cr23Sketch N t C x) [])
    (decoderStart_cr23_pc N t C x) (decoderStart_cr23_r0 N t C x)
    (decoderStart_cr23_pay N t C x) (decoderStart_cr23_zero N t C x)
  refine halts_of_run progDec (detEnv (cr23Word N) (cr23DecDet N t C)) 0 decStmt.len
    (decoderStart (cr23Word N) (cr23Sketch N t C x) [])
    ((decStmtCost N t : ℝ) + 1)
    (fun k s' => k ≤ decStmtCost N t ∧ OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t)
    (fun s' => OutputsSupport s' x ∧ s'.regs r0 = decOutBase N t) progDec_at_halt hsem ?_
  rintro k s' ⟨hk, hout, hr0⟩
  refine ⟨?_, hout, hr0⟩
  have hk' : (k : ℝ) ≤ (decStmtCost N t : ℝ) := by exact_mod_cast hk
  linarith

end LinearSetReconciliation327.Main


