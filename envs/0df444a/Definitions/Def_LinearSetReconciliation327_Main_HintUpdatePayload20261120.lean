-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpdatePayload20261120
-- name    : LinearSetReconciliation327_Main_HintUpdatePayload20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:45:50.850005+00:00
-- url     : https://prove2.me/theorems/882548cc-4953-43da-abc9-37a2ff0a4611
-- title:
--   LinearSetReconciliation327 — HintUpdatePayload (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpdatePayload20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upSavedBody_raw_of_view (E : RAMEnv) (base betaDet betaPay i ptr words : ℕ)
    (it : UpIt) (ab : UpAbs) (p : RAMState)
    (hView : UpBasedView E.W betaPay ab p) (hRaw : UpBasedRawPayload betaPay words ab p)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + words ≤ 2 ^ E.W)
    (hKind : UpItemKind it) (h6 : p.regs 6 = 1) (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay)
    (h7 : (upBasedBodyResult E base p).regs 7 = ptr + 16) (h16 : ptr + 16 < 2 ^ E.W)
    (hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = it.mode)
    (hSav : E.det ((betaDet + (ptr + 15)) % 2 ^ E.W) % 2 ^ E.W = it.sav)
    (hData : UpBasedPrefixData E betaDet betaPay i it ab p (upBasedPrefixRun E p))
    (hOutView : UpBasedView E.W betaPay (upApply (upShiftDetEnv E betaDet) i it ab)
      (upSavedBodyResult E base p)) :
    UpBasedRawPayload betaPay words (upApply (upShiftDetEnv E betaDet) i it ab)
      (upSavedBodyResult E base p) := by
  let F := upShiftDetEnv E betaDet
  let q := upBasedBodyResult E base p
  have hB := upBasedBody_view_of_data E base betaDet betaPay i it ab p hView hPay hData
  have hRawB := upBasedBody_raw_of_data E base betaDet betaPay i words it ab p hView hRaw hPay hEnd hData
  have hQ := upBasedBodyResult_meta E base p
  have hQ6 : q.regs 6 = 1 := (hQ.2.2.2 6 (by tauto)).trans h6
  have hQ14 : q.regs 14 = betaDet := (hQ.2.2.2 14 (by tauto)).trans h14
  have hQ15 : q.regs 15 = betaPay := (hQ.2.2.2 15 (by tauto)).trans h15
  have hQc : q.regs 8 < 2 ^ E.W := by
    rw [hB.coord]
    exact Nat.mod_lt _ (Nat.two_pow_pos E.W)
  have hQf : q.regs 9 < 2 ^ E.W := by
    rw [hB.flag]
    exact Nat.mod_lt _ (Nat.two_pow_pos E.W)
  have hPost := upSavedPost_memory E betaDet betaPay ptr it q hKind hQ6 hQ14 hQ15 h7 h16 hMode hSav hQc hQf
  have hOut := upSavedBodyResult_data E base p
  apply upBasedRaw_initial E.W betaPay words _ _ hOutView hEnd
  intro j hj
  rw [hOut.1]
  apply hPost.1
  rw [hRawB j hj]
  exact upBasedView_bound E.W betaPay _ q hB j

theorem upSavedBody_payload (E : RAMEnv) (p : RAMState) (base betaDet betaPay i j words : ℕ)
    (it : UpIt) (ab : UpAbs)
    (hView : UpBasedView E.W betaPay ab p) (hRaw : UpBasedRawPayload betaPay words ab p)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + words ≤ 2 ^ E.W)
    (hW : 1 < 2 ^ E.W) (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W)
    (hKind : UpItemKind it) (hSlots : 2 ≤ it.mode → it.sav + 1 < 2 ^ E.W)
    (h0 : p.regs 0 = i) (h5 : p.regs 5 = j) (h6 : p.regs 6 = 1)
    (h7 : p.regs 7 = 8 + 16 * j) (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay)
    (hAddr : 8 + 16 * (j + 1) < 2 ^ E.W)
    (hFields : ∀ t, t < 16 → (upShiftDetEnv E betaDet).det (8 + 16 * j + t) % 2 ^ E.W = it.fld t)
    (hWidth : upvWw (upShiftDetEnv E betaDet) = E.W) :
    UpBasedView E.W betaPay (upApply (upShiftDetEnv E betaDet) i it ab) (upSavedBodyResult E base p) ∧
      UpBasedRawPayload betaPay words (upApply (upShiftDetEnv E betaDet) i it ab) (upSavedBodyResult E base p) := by
  let ptr := 8 + 16 * j
  have h16 : ptr + 16 < 2 ^ E.W := by dsimp [ptr]; omega
  have hCounter : (p.regs 5 + p.regs 6) % 2 ^ E.W = j + 1 := by
    rw [h5, h6, Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ E.W)]
  have hNext : (upBasedBodyResult E base p).regs 7 = ptr + 16 := by
    have hN := upBasedBodyResult_pointer E base p (by omega) (by omega)
      (by rw [hCounter]; exact hAddr)
    rw [hCounter] at hN
    exact hN.trans (by dsimp [ptr]; omega)
  have hData := upBasedPrefix_data E p betaDet betaPay i ptr it ab hView hW h0
    (by simpa only [Nat.mod_eq_of_lt hW] using h6) h7 h14 h15 h16 hFields hWidth
  have hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = it.mode := by
    simpa only [upShiftDetEnv, UpIt.fld] using hFields 10 (by decide)
  have hSav : E.det ((betaDet + (ptr + 15)) % 2 ^ E.W) % 2 ^ E.W = it.sav := by
    simpa only [upShiftDetEnv, UpIt.fld] using hFields 15 (by decide)
  have hV := upSavedBody_view_of_data E base betaDet betaPay i ptr it ab p hView hPay hW hc hf hKind hSlots
    h6 h14 h15 hNext h16 hMode hSav hData
  have hR := upSavedBody_raw_of_view E base betaDet betaPay i ptr words it ab p hView hRaw hPay hEnd
    hKind h6 h14 h15 hNext h16 hMode hSav hData hV
  exact ⟨hV, hR⟩

end LinearSetReconciliation327.Main

namespace LinearSetReconciliation327.Main
theorem upSavedLoopState_payload (E : RAMEnv)
    (head betaDet betaPay i words : ℕ) (items : List UpIt) (seed : RAMState) (ab : UpAbs)
    (hLayout : UpSavedLayout E betaDet items)
    (hView : UpBasedView E.W betaPay ab seed) (hRaw : UpBasedRawPayload betaPay words ab seed)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + words ≤ 2 ^ E.W)
    (h16 : 16 < 2 ^ E.W) (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W)
    (hReady : UpSavedReady betaDet items.length 0 seed) (hPtr : seed.regs 7 = 8)
    (h0 : seed.regs 0 = i) (h15 : seed.regs 15 = betaPay)
    (hCount : E.det (betaDet % 2 ^ E.W) % 2 ^ E.W = items.length) :
    ∀ j, j ≤ items.length →
      UpBasedView E.W betaPay (upFold (upShiftDetEnv E betaDet) i ab (items.take j))
        (upSavedLoopState E head seed j) ∧
      UpBasedRawPayload betaPay words (upFold (upShiftDetEnv E betaDet) i ab (items.take j))
        (upSavedLoopState E head seed j) := by
  have hW : 1 < 2 ^ E.W := by omega
  have hL : items.length < 2 ^ E.W := by have hh := hLayout.end_addr; omega
  have hReadyAll := upSavedLoopState_ready E head betaDet items.length seed hReady hL hCount
  have hPtrAll := upSavedLoopState_pointer E head betaDet items.length seed hReady hPtr hL hCount h16 hLayout.end_addr
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · simpa only [List.take_zero, upFold, upSavedLoopState_zero] using hView
      · simpa only [List.take_zero, upFold, upSavedLoopState_zero] using hRaw
  | succ j ih =>
      intro hj
      have hjL : j < items.length := by omega
      have hPrev := ih (by omega)
      let p := upSavedLoopState E head seed j
      let entry : RAMState := { runBlock upBasedTest.code E p with pc := head + 2 }
      let a := upFold (upShiftDetEnv E betaDet) i ab (items.take j)
      let it := items[j]'hjL
      have hMemEntry : entry.mem = p.mem := upBasedTest_mem E p
      have hEntryView : UpBasedView E.W betaPay a entry :=
        upBasedView_data E.W betaPay a p entry hPrev.1 hMemEntry
          (upBasedTest_frame E p 8 (by decide)) (upBasedTest_frame E p 9 (by decide))
      have hEntryRaw : UpBasedRawPayload betaPay words a entry := by
        intro q hq
        rw [hMemEntry]
        exact hPrev.2 q hq
      have hR := hReadyAll j hjL.le
      have hE0 : entry.regs 0 = i := (upBasedTest_frame E p 0 (by decide)).trans
        ((upSavedLoopState_frame E head seed 0 (Or.inl rfl) j).trans h0)
      have hE5 : entry.regs 5 = j := (upBasedTest_frame E p 5 (by decide)).trans hR.counter
      have hE6 : entry.regs 6 = 1 := (upBasedTest_frame E p 6 (by decide)).trans hR.one
      have hE7 : entry.regs 7 = 8 + 16 * j := (upBasedTest_frame E p 7 (by decide)).trans (hPtrAll j hjL.le)
      have hE14 : entry.regs 14 = betaDet := (upBasedTest_frame E p 14 (by decide)).trans hR.base
      have hE15 : entry.regs 15 = betaPay := (upBasedTest_frame E p 15 (by decide)).trans
        ((upSavedLoopState_frame E head seed 15 (Or.inr (Or.inr rfl)) j).trans h15)
      have hCF := upFold_cf_bound (upShiftDetEnv E betaDet) i (items.take j) ab hc hf
      have hMember : it ∈ items := List.getElem_mem hjL
      have hEff := upSavedBody_payload E entry (head + 2) betaDet betaPay i j words it a hEntryView hEntryRaw hPay hEnd
        hW hCF.1 hCF.2 (hLayout.kind it hMember) (hLayout.slots it hMember)
        hE0 hE5 hE6 hE7 hE14 hE15 (by have hh := hLayout.end_addr; omega)
        (hLayout.fields j hjL) hLayout.width
      have hFold := upFold_take_succ (upShiftDetEnv E betaDet) i items ab j hjL
      refine ⟨?_, ?_⟩
      · rw [hFold, upSavedLoopState_succ, upSavedLoopStep_eq]
        exact ⟨hEff.1.mem, hEff.1.coord, hEff.1.flag⟩
      · rw [hFold, upSavedLoopState_succ, upSavedLoopStep_eq]
        exact hEff.2
theorem upSavedSup_payload_sem (P : Program) (E : RAMEnv)
    (base betaDet betaPay i words : ℕ) (items : List UpIt) (s : RAMState) (ab : UpAbs)
    (hAt : At P base (upSavedSup.compile base)) (hpc : s.pc = base)
    (hLayout : UpSavedLayout E betaDet items)
    (hMem : upVirtualMem E.W betaPay s.mem = ab.mem) (hc0 : ab.c = 0) (hf1 : ab.f = 1)
    (hRaw : UpBasedRawPayload betaPay words ab s)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + words ≤ 2 ^ E.W)
    (h16 : 16 < 2 ^ E.W) (h0 : s.regs 0 = i) (h14 : s.regs 14 = betaDet) (h15 : s.regs 15 = betaPay)
    (hCount : E.det (betaDet % 2 ^ E.W) % 2 ^ E.W = items.length) :
    Sem P E base (base + 156) s
      (fun k out => k ≤ 147 * items.length + 10 ∧
        UpBasedView E.W betaPay (upFold (upShiftDetEnv E betaDet) i ab items) out ∧
        UpBasedRawPayload betaPay words (upFold (upShiftDetEnv E betaDet) i ab items) out ∧
        out.regs 0 = s.regs 0 ∧ out.regs 14 = betaDet ∧ out.regs 15 = betaPay) := by
  have hW : 1 < 2 ^ E.W := by omega
  have h8 : 8 < 2 ^ E.W := by omega
  have hL : items.length < 2 ^ E.W := by have hh := hLayout.end_addr; omega
  let seed := upBasedPrologueRun E s
  obtain ⟨hPpc, hP5, hP6, hP7, hP8, hP9, hP1, hPm, hPfr⟩ := upBasedPrologue_meta E s hW h8
  have hSeedView : UpBasedView E.W betaPay ab seed :=
    ⟨by rw [hPm]; exact hMem, hP8.trans hc0.symm, hP9.trans hf1.symm⟩
  have hSeedRaw : UpBasedRawPayload betaPay words ab seed := by
    intro q hq
    rw [hPm]
    exact hRaw q hq
  have hSeedReady : UpSavedReady betaDet items.length 0 seed :=
    ⟨hP5, hP6, (by rw [hP1, h14, hCount]), (hPfr 14 (by tauto)).trans h14⟩
  have hFold := upSavedLoopState_payload E (base + 8) betaDet betaPay i words items seed ab
    hLayout hSeedView hSeedRaw hPay hEnd h16 (by rw [hc0]; exact Nat.two_pow_pos E.W)
    (by rw [hf1]; exact hW) hSeedReady hP7 ((hPfr 0 (by tauto)).trans h0)
    ((hPfr 15 (by tauto)).trans h15) hCount items.length le_rfl
  simp only [List.take_length] at hFold
  have hResultView : UpBasedView E.W betaPay (upFold (upShiftDetEnv E betaDet) i ab items)
      (upSavedSupResult E base s items.length) := by
    rw [upSavedSupResult_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact (congrArg (upVirtualMem E.W betaPay) (upBasedTest_mem E _)).trans hFold.1.mem
    · exact (upBasedTest_frame E _ 8 (by decide)).trans hFold.1.coord
    · exact (upBasedTest_frame E _ 9 (by decide)).trans hFold.1.flag
  have hResultRaw : UpBasedRawPayload betaPay words (upFold (upShiftDetEnv E betaDet) i ab items)
      (upSavedSupResult E base s items.length) := by
    intro q hq
    rw [upSavedSupResult_eq, upBasedTest_mem]
    exact hFold.2 q hq
  have hExec := upSavedSup_sem P E base items.length s hAt hW h8 hL
    (by rw [h14]; exact hCount) hpc
  apply Sem.mono hExec
  intro k out hk
  refine ⟨hk.1, ?_, ?_, hk.2.2.1, hk.2.2.2.1.trans h14, hk.2.2.2.2.trans h15⟩
  · rw [hk.2.1]
    exact hResultView
  · rw [hk.2.1]
    exact hResultRaw


end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.upSavedSup_payload_sem


