-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpdateExport20261120
-- name    : LinearSetReconciliation327_Main_HintUpdateExport20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:47:25.096827+00:00
-- url     : https://prove2.me/theorems/5a984888-b371-4109-a517-4b34e99a3805
-- title:
--   LinearSetReconciliation327 — HintUpdateExport (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpdateExport20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateRoot20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpdatePayload20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def UpWordState (E : RAMEnv) (s : RAMState) : Prop :=
  (∀ r, s.regs r < 2 ^ E.W) ∧ ∀ a, s.mem a < 2 ^ E.W

theorem upExec_word_bound (op : Instr) (E : RAMEnv) (s : RAMState) (h : UpWordState E s) :
    UpWordState E (execInstr op E s) := by
  rcases h with ⟨hr, hm⟩
  cases op <;> constructor <;> intro a <;>
    simp only [execInstr, Function.update_apply] <;> (try split_ifs) <;>
    first | exact Nat.mod_lt _ (Nat.two_pow_pos E.W) | exact hr _ | exact hm _

theorem upStep_word_bound (G : Program) (E : RAMEnv) (s : RAMState) (h : UpWordState E s) :
    UpWordState E (step G E s) := by
  cases hg : G[s.pc]? with
  | none => simpa only [step, hg] using h
  | some op =>
      rw [step_eq_execInstr G E s op hg]
      exact upExec_word_bound op E s h

theorem upIterate_word_bound (G : Program) (E : RAMEnv) (s : RAMState) (k : ℕ) (h : UpWordState E s) :
    UpWordState E ((step G E)^[k] s) := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
      rw [iterate_succ_apply_front]
      exact ih _ (upStep_word_bound G E s h)

theorem upExec_high_frame (op : Instr) (E : RAMEnv) (s : RAMState)
    (hr : ∀ r, s.regs r < 2 ^ E.W) (addr : ℕ) (ha : 2 ^ E.W ≤ addr) :
    (execInstr op E s).mem addr = s.mem addr := by
  cases op <;> try rfl
  case store a v =>
    simp only [execInstr, Function.update_apply]
    rw [if_neg (by have hh := hr a; omega : addr ≠ s.regs a)]

theorem upStep_high_frame (G : Program) (E : RAMEnv) (s : RAMState)
    (hr : ∀ r, s.regs r < 2 ^ E.W) (addr : ℕ) (ha : 2 ^ E.W ≤ addr) :
    (step G E s).mem addr = s.mem addr := by
  cases hg : G[s.pc]? with
  | none => simp only [step, hg]
  | some op =>
      rw [step_eq_execInstr G E s op hg]
      exact upExec_high_frame op E s hr addr ha

theorem upIterate_high_frame (G : Program) (E : RAMEnv) (s : RAMState) (k : ℕ)
    (h : UpWordState E s) (addr : ℕ) (ha : 2 ^ E.W ≤ addr) :
    ((step G E)^[k] s).mem addr = s.mem addr := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [iterate_succ_apply_front]
      exact (ih _ (upStep_word_bound G E s h)).trans (upStep_high_frame G E s h.1 addr ha)

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def UpTwoRegion (beta payload workStart workEnd addr : ℕ) : Prop :=
  (beta ≤ addr ∧ addr < beta + payload) ∨ (beta + workStart ≤ addr ∧ addr < beta + workEnd)

theorem upVirtualMem_two_region_frame (W beta payload workStart workEnd : ℕ) (p q : RAMState)
    (hBeta : beta < 2 ^ W) (hEnd : beta + workEnd ≤ 2 ^ W)
    (hGap : payload ≤ workStart) (hWork : workStart ≤ workEnd)
    (hIn : ∀ addr, p.mem addr < 2 ^ W) (hOut : ∀ addr, q.mem addr < 2 ^ W)
    (hHigh : ∀ addr, 2 ^ W ≤ addr → q.mem addr = p.mem addr)
    (hVirtual : ∀ a, a < 2 ^ W → ¬ (a < payload ∨ (workStart ≤ a ∧ a < workEnd)) →
      upVirtualMem W beta q.mem a = upVirtualMem W beta p.mem a) :
    UpMemFrame (UpTwoRegion beta payload workStart workEnd) p q := by
  intro addr hOutside
  by_cases hAddr : addr < 2 ^ W
  · let a := if beta ≤ addr then addr - beta else addr + 2 ^ W - beta
    have hA : a < 2 ^ W := by
      dsimp [a]
      split_ifs <;> omega
    have hCyclic : upCyclicAddr W beta a = addr := by
      by_cases hb : beta ≤ addr
      · have hVal : a = addr - beta := by simp only [a, if_pos hb]
        rw [hVal]
        have hAdd : beta + (addr - beta) = addr := by omega
        simp only [upCyclicAddr, hAdd, Nat.mod_eq_of_lt hAddr]
      · have hVal : a = addr + 2 ^ W - beta := by simp only [a, if_neg hb]
        rw [hVal]
        have hAdd : beta + (addr + 2 ^ W - beta) = addr + 2 ^ W := by omega
        simp only [upCyclicAddr, hAdd, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
          Nat.mod_eq_of_lt hAddr]
    have hOutsideSource : ¬ (a < payload ∨ (workStart ≤ a ∧ a < workEnd)) := by
      intro hs
      rcases hs with hs | hs
      · by_cases hb : beta ≤ addr
        · have hVal : a = addr - beta := by simp only [a, if_pos hb]
          exact hOutside (Or.inl ⟨hb, by omega⟩)
        · have hVal : a = addr + 2 ^ W - beta := by simp only [a, if_neg hb]
          omega
      · by_cases hb : beta ≤ addr
        · have hVal : a = addr - beta := by simp only [a, if_pos hb]
          exact hOutside (Or.inr ⟨by omega, by omega⟩)
        · have hVal : a = addr + 2 ^ W - beta := by simp only [a, if_neg hb]
          omega
    have hQ : upVirtualMem W beta q.mem a = q.mem addr := by
      rw [upVirtualMem, if_pos hA, hCyclic, Nat.mod_eq_of_lt (hOut addr)]
    have hP : upVirtualMem W beta p.mem a = p.mem addr := by
      rw [upVirtualMem, if_pos hA, hCyclic, Nat.mod_eq_of_lt (hIn addr)]
    exact hQ.symm.trans ((hVirtual a hA hOutsideSource).trans hP)
  · exact hHigh addr (by omega)

end LinearSetReconciliation327.Main

set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main

theorem upFold_root_two_region_frame (CR : CRFamily) (E : RAMEnv)
    (Bc colBase payload workStart sav : ℕ) (T : Node) (r : T.Seed) (i : ℕ)
    (hW : 1 < 2 ^ E.W) (hN : 0 < T.N) (hNM : T.N ≤ 2 ^ E.W) (hi : i < T.N)
    (hLocal : UpLocalTree CR E i Bc colBase T r 0 0 0)
    (hFit : synLen CR T ≤ payload * E.W) (hWork : payload ≤ workStart)
    (hRoom : UpSaveRoom workStart sav T)
    (mem : ℕ → ℕ) (hm : ∀ a, mem a < 2 ^ E.W) :
    ∀ a, ¬ (a < payload ∨ (workStart ≤ a ∧ a < sav + 2)) →
      (upFold E i (⟨mem, 0, 1⟩ : UpAbs) (upSched CR Bc colBase T 0 0 0 sav [])).mem a = mem a := by
  have hFitWork : synLen CR T ≤ workStart * E.W := hFit.trans (Nat.mul_le_mul_right E.W hWork)
  have hPure := upFold_root_of_local CR E Bc colBase workStart sav T r i hW hN hNM hLocal hFitWork hRoom hi mem hm
  have hBits : ∀ b ∈ bitBlock CR T r {i} 0, b < payload * E.W :=
    up_bitBlock_fits CR E.W payload T r 0 {i} (by simpa only [Nat.zero_add] using hFit)
  intro a hOutside
  have haPayload : payload ≤ a := by by_contra h; exact hOutside (Or.inl (by omega))
  by_cases haWork : a < workStart
  · rw [hPure a haWork, up_packSel_above E.W payload _ hBits a haPayload, Nat.xor_zero]
  · have haHigh : sav + 2 ≤ a := by
      by_contra h
      exact hOutside (Or.inr ⟨by omega, by omega⟩)
    have hiW : i < 2 ^ E.W := hi.trans_le hNM
    have hReset := upReset_apply_mod E i T.N (⟨mem, 0, 1⟩ : UpAbs)
      hW hN hNM hiW (Nat.two_pow_pos E.W) hW hm
    rw [Nat.mod_eq_of_lt hi] at hReset
    have hTree := upFold_tree_of_local CR E i Bc colBase workStart hW T r 0 0 0 sav hLocal
      (by simpa only [Nat.zero_add] using hFitWork) hRoom i 1 hi hiW hW (Or.inr rfl) mem hm
    rw [upSched_root, upFold, hReset]
    simpa only [if_pos rfl, if_pos trivial] using hTree.2 a haHigh

end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main

theorem upSavedSup_toggle_frame_sem (G : Program) (E : RAMEnv)
    (CR : CRFamily) (P : HintParams) (T : Node) (hT : IsSchemeTree P T) (r : (hintSpec T).Seed)
    (base betaDet betaPay Bc colBase workStart sav : ℕ) (items : List UpIt)
    (hItems : items = upSched CR Bc colBase T 0 0 0 sav [])
    (y : Fin (synLen CR T) → ZMod 2) (i : Fin T.N) (s : RAMState)
    (hAt : At G base (upSavedSup.compile base)) (hpc : s.pc = base)
    (hLayout : UpSavedLayout E betaDet items) (hState : UpWordState E s)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + (sav + 2) ≤ 2 ^ E.W)
    (hGap : wordsOf E.W (synLen CR T) ≤ workStart)
    (h16 : 16 < 2 ^ E.W) (hNM : T.N ≤ 2 ^ E.W)
    (h0 : s.regs 0 = i.val) (h14 : s.regs 14 = betaDet) (h15 : s.regs 15 = betaPay)
    (hCount : E.det (betaDet % 2 ^ E.W) % 2 ^ E.W = items.length)
    (hPayload : ∀ q, q < wordsOf E.W (synLen CR T) → s.mem (betaPay + q) = packMem E.W y q)
    (hLocal : UpLocalTree CR (upShiftDetEnv E betaDet) i.val Bc colBase T (hintKappa P T hT r) 0 0 0)
    (hRoom : UpSaveRoom workStart sav T) :
    Sem G E base (base + 156) s
      (fun k out => k ≤ 147 * items.length + 10 ∧
        (∀ q, q < wordsOf E.W (synLen CR T) →
          out.mem (betaPay + q) = packMem E.W (y + hintH_trees CR P T hT r (Pi.single i 1)) q) ∧
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
  have hPayloadRoom : UpSaveRoom (wordsOf E.W (synLen CR T)) sav T := by
    unfold UpSaveRoom at hRoom ⊢
    omega
  let ab : UpAbs := ⟨upVirtualMem E.W betaPay s.mem, 0, 1⟩
  have hRaw : UpBasedRawPayload betaPay (wordsOf E.W (synLen CR T)) ab s := by
    intro q hq
    have hQ : q < 2 ^ E.W := by omega
    have hAddr : betaPay + q < 2 ^ E.W := by omega
    change s.mem (betaPay + q) = upVirtualMem E.W betaPay s.mem q
    rw [upVirtualMem, if_pos hQ, upCyclicAddr, Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt (hState.2 (betaPay + q))]
  have hFit := up_words_cover E.W (synLen CR T) hWpos
  have hPure := upFold_root_of_local CR (upShiftDetEnv E betaDet) Bc colBase
    (wordsOf E.W (synLen CR T)) sav T (hintKappa P T hT r) i.val hW
    (by have hh := i.isLt; omega) hNM hLocal hFit hPayloadRoom i.isLt
    (upVirtualMem E.W betaPay s.mem) (upVirtualMem_lt E.W betaPay s.mem)
  have hPureFrame := upFold_root_two_region_frame CR (upShiftDetEnv E betaDet) Bc colBase
    (wordsOf E.W (synLen CR T)) workStart sav T (hintKappa P T hT r) i.val hW
    (by have hh := i.isLt; omega) hNM i.isLt hLocal hFit hGap hRoom
    (upVirtualMem E.W betaPay s.mem) (upVirtualMem_lt E.W betaPay s.mem)
  rw [← hItems] at hPure hPureFrame
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
        packSel E.W (bitBlock CR T (hintKappa P T hT r) {i.val} 0) q := hPure q hq
    _ = packMem E.W y q ^^^ packSel E.W (bitBlock CR T (hintKappa P T hT r) {i.val} 0) q := by
      have hIn : upVirtualMem E.W betaPay s.mem q = packMem E.W y q :=
        (show s.mem (betaPay + q) = upVirtualMem E.W betaPay s.mem q from hRaw q hq).symm.trans (hPayload q hq)
      rw [hIn]
    _ = packMem E.W (y + hintH_trees CR P T hT r (Pi.single i 1)) q :=
      (packMem_add_H_single CR P T hT r E.W hWpos y i q).symm

end LinearSetReconciliation327.Main
end
namespace LinearSetReconciliation327.Main

theorem upInit_word_bound (E : RAMEnv) {N M : ℕ} (y : Fin M → ZMod 2) (i : Fin N)
    (hW : 0 < E.W) (hN : N ≤ 2 ^ E.W) : UpWordState E (initState (packMem E.W y) i.val 0 0) := by
  constructor
  · intro r
    simp only [initState]
    split_ifs <;> first | exact i.isLt.trans_le hN | exact Nat.two_pow_pos E.W
  · intro a
    exact packMem_lt E.W hW y a

theorem up5Sem_togglesWithin (E : RAMEnv) {N M : ℕ}
    (H : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)) (Sup : Stmt) (prog : Program) (B : ℝ)
    (hCompile : Sup.compile 0 ++ [Instr.halt] = prog) (hW : 0 < E.W) (hN : N ≤ 2 ^ E.W)
    (hSem : ∀ (y : Fin M → ZMod 2) (i : Fin N) (s : RAMState),
      UpWordState E s → s.pc = 0 → s.regs 0 = i.val →
      (∀ q, q < wordsOf E.W M → s.mem q = packMem E.W y q) →
      Sem prog E 0 Sup.len s (fun k out => (k : ℝ) ≤ B ∧
        ∀ q, q < wordsOf E.W M → out.mem q = packMem E.W (y + H (Pi.single i 1)) q)) :
    TogglesWithin prog E H B := by
  intro y i
  let s := initState (packMem E.W y) i.val 0 0
  obtain ⟨_, k, out, hRun, hExit, hCost, hPayload⟩ := hSem y i s
    (upInit_word_bound E y i hW hN) rfl (by simp [s, initState]) (by intro q hq; rfl)
  have hHalt : Halted prog out := by
    unfold Halted
    rw [← hCompile, hExit, ← Stmt.length_compile Sup 0]
    simp
  exact ⟨out, ⟨k, hCost, hRun, hHalt⟩, hPayload⟩

end LinearSetReconciliation327.Main

namespace LinearSetReconciliation327.Main
def progUpSaved : Program := upSavedSup.compile 0 ++ [Instr.halt]
theorem upSavedSup_len : upSavedSup.len = 156 := rfl
theorem upSavedSup_program_eq : upSavedSup.compile 0 ++ [Instr.halt] = progUpSaved := rfl
end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.upSavedSup_toggle_frame_sem
#print axioms LinearSetReconciliation327.Main.up5Sem_togglesWithin


