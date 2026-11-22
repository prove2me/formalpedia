-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintChildToggle20261120
-- name    : LinearSetReconciliation327_Main_HintChildToggle20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:48:52.731828+00:00
-- url     : https://prove2.me/theorems/797fa8cf-fa9d-4e77-a01b-32f0fc1ec0b7
-- title:
--   LinearSetReconciliation327 — HintChildToggle (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintChildToggle20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateExport20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable section

/-- Start a subtree update at its global random-table index. The entry RESET
sets its coordinate just as the root updater does. -/
def hintChildUpdateSchedule (CR : CRFamily) (Bc colBase : ℕ) (T : Node) (node sav : ℕ) : List UpIt :=
  upReset T.N :: (upOwnItems CR Bc colBase T node 0 0 ++ upKids CR Bc colBase T node 0 0 sav [])

def hintChildToggleVec (CR : CRFamily) (T : Node) (r : T.Seed) (i : Fin T.N) :
    Fin (synLen CR T) → ZMod 2 :=
  fun p => bitVal CR T r p {i.val}

theorem hintPackMem_add_child (CR : CRFamily) (T : Node) (r : T.Seed)
    (W : ℕ) (hW : 0 < W) (y : Fin (synLen CR T) → ZMod 2) (i : Fin T.N) (a : ℕ) :
    packMem W (y + hintChildToggleVec CR T r i) a =
      packMem W y a ^^^ packSel W (bitBlock CR T r {i.val} 0) a := by
  rw [packMem_add W hW, packMem_eq_packSel W hW (hintChildToggleVec CR T r i)]
  apply congrArg (fun B : Finset ℕ => packMem W y a ^^^ packSel W B a)
  ext q
  simp only [hintChildToggleVec, bitBlock, colSupp, Nat.zero_add, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, he⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, he⟩

theorem hintChildToggle_sem (G : Program) (E : RAMEnv)
    (CR : CRFamily) (T : Node) (r : T.Seed) (node : ℕ)
    (base betaDet betaPay Bc colBase workStart sav : ℕ) (items : List UpIt)
    (hItems : items = hintChildUpdateSchedule CR Bc colBase T node sav)
    (y : Fin (synLen CR T) → ZMod 2) (i : Fin T.N) (s : RAMState)
    (hAt : At G base (upSavedSup.compile base)) (hpc : s.pc = base)
    (hLayout : UpSavedLayout E betaDet items) (hState : UpWordState E s)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + (sav + 2) ≤ 2 ^ E.W)
    (hGap : wordsOf E.W (synLen CR T) ≤ workStart)
    (h16 : 16 < 2 ^ E.W) (hNM : T.N ≤ 2 ^ E.W)
    (h0 : s.regs 0 = i.val) (h14 : s.regs 14 = betaDet) (h15 : s.regs 15 = betaPay)
    (hCount : E.det (betaDet % 2 ^ E.W) % 2 ^ E.W = items.length)
    (hPayload : ∀ q, q < wordsOf E.W (synLen CR T) → s.mem (betaPay + q) = packMem E.W y q)
    (hLocal : UpLocalTree CR (upShiftDetEnv E betaDet) i.val Bc colBase T r node 0 0)
    (hRoom : UpSaveRoom workStart sav T) :
    Sem G E base (base + 156) s
      (fun k out => k ≤ 147 * items.length + 10 ∧
        (∀ q, q < wordsOf E.W (synLen CR T) →
          out.mem (betaPay + q) = packMem E.W (y + hintChildToggleVec CR T r i) q) ∧
        UpMemFrame (UpTwoRegion betaPay (wordsOf E.W (synLen CR T)) workStart (sav + 2)) s out ∧
        out.regs 0 = s.regs 0 ∧ out.regs 14 = betaDet ∧ out.regs 15 = betaPay ∧ UpWordState E out) := by
  have hW : 1 < 2 ^ E.W := by omega
  have hWpos : 0 < E.W := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp only [hz, pow_zero] at h16
    omega
  have hWork : workStart ≤ sav + 2 := by have hh := hRoom; unfold UpSaveRoom at hh; omega
  have hPayEnd : betaPay + wordsOf E.W (synLen CR T) ≤ 2 ^ E.W := by omega
  let ab : UpAbs := ⟨upVirtualMem E.W betaPay s.mem, 0, 1⟩
  have hRaw : UpBasedRawPayload betaPay (wordsOf E.W (synLen CR T)) ab s := by
    intro q hq
    have hQ : q < 2 ^ E.W := by omega
    have hAddr : betaPay + q < 2 ^ E.W := by omega
    change s.mem (betaPay + q) = upVirtualMem E.W betaPay s.mem q
    rw [upVirtualMem, if_pos hQ, upCyclicAddr, Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt (hState.2 (betaPay + q))]
  have hFit := up_words_cover E.W (synLen CR T) hWpos
  have hRawBound := upVirtualMem_lt E.W betaPay s.mem
  have hI := i.isLt
  have hIFit := hI.trans_le hNM
  have hReset := upReset_apply_mod (upShiftDetEnv E betaDet) i.val T.N ab
    hW (by omega) hNM hIFit (by exact Nat.two_pow_pos E.W) hW hRawBound
  rw [Nat.mod_eq_of_lt hI] at hReset
  have hFold := upFold_tree_of_local CR (upShiftDetEnv E betaDet) i.val Bc colBase workStart hW T r node 0 0 sav
    hLocal (by
      change 0 + synLen CR T ≤ workStart * E.W
      simpa only [Nat.zero_add] using hFit.trans (Nat.mul_le_mul_right E.W hGap))
    hRoom i.val 1 hI hIFit hW (Or.inr rfl) ab.mem hRawBound
  have hLow (q : ℕ) (hq : q < workStart) :
      (upFold (upShiftDetEnv E betaDet) i.val ab items).mem q =
        ab.mem q ^^^ packSel E.W (bitBlock CR T r {i.val} 0) q := by
    rw [hItems, hintChildUpdateSchedule, upFold, hReset]
    simpa only [upShiftDetEnv, if_pos rfl, if_pos trivial] using hFold.1 q hq
  have hPureFrame (q : ℕ)
      (hOutside : ¬ (q < wordsOf E.W (synLen CR T) ∨ (workStart ≤ q ∧ q < sav + 2))) :
      (upFold (upShiftDetEnv E betaDet) i.val ab items).mem q = ab.mem q := by
    have hq := not_or.mp hOutside
    by_cases hb : q < workStart
    · have hBits : ∀ b ∈ bitBlock CR T r {i.val} 0, b < wordsOf E.W (synLen CR T) * E.W :=
        up_bitBlock_fits CR E.W _ T r 0 {i.val} (by simpa only [Nat.zero_add] using hFit)
      rw [hLow q hb, up_packSel_above E.W _ _ hBits q (by omega), Nat.xor_zero]
    · rw [hItems, hintChildUpdateSchedule, upFold, hReset]
      exact hFold.2 q (by omega)
  have hExec := upSavedSup_payload_sem G E base betaDet betaPay i.val
    (wordsOf E.W (synLen CR T)) items s ab hAt hpc hLayout rfl rfl rfl hRaw hPay hPayEnd h16 h0 h14 h15 hCount
  obtain ⟨hStart, k, out, hRun, hExit, hCost, hView, hRawOut, hR0, hR14, hR15⟩ := hExec
  have hBoundOut : UpWordState E out := hRun ▸ upIterate_word_bound G E s k hState
  have hHigh : ∀ addr, 2 ^ E.W ≤ addr → out.mem addr = s.mem addr := by
    intro addr ha
    rw [← hRun]
    exact upIterate_high_frame G E s k hState addr ha
  have hFrame := upVirtualMem_two_region_frame E.W betaPay (wordsOf E.W (synLen CR T)) workStart
    (sav + 2) s out hPay hEnd hGap hWork hState.2 hBoundOut.2 hHigh (by
      intro a ha hOutside
      rw [hView.mem]
      exact hPureFrame a hOutside)
  refine ⟨hStart, k, out, hRun, hExit, hCost, ?_, hFrame, hR0, hR14, hR15, hBoundOut⟩
  intro q hq
  calc
    out.mem (betaPay + q) = (upFold (upShiftDetEnv E betaDet) i.val ab items).mem q := hRawOut q hq
    _ = upVirtualMem E.W betaPay s.mem q ^^^
        packSel E.W (bitBlock CR T r {i.val} 0) q := hLow q (hq.trans_le hGap)
    _ = packMem E.W y q ^^^ packSel E.W (bitBlock CR T r {i.val} 0) q := by
      have hIn : upVirtualMem E.W betaPay s.mem q = packMem E.W y q :=
        (show s.mem (betaPay + q) = upVirtualMem E.W betaPay s.mem q from hRaw q hq).symm.trans (hPayload q hq)
      rw [hIn]
    _ = packMem E.W (y + hintChildToggleVec CR T r i) q :=
      (hintPackMem_add_child CR T r E.W hWpos y i q).symm

end
end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildToggle_sem


