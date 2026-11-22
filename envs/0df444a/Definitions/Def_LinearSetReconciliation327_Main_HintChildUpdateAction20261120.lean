-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintChildUpdateAction20261120
-- name    : LinearSetReconciliation327_Main_HintChildUpdateAction20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:03:02.222923+00:00
-- url     : https://prove2.me/theorems/a81c99cb-e883-4d50-a464-3571288a0361
-- title:
--   LinearSetReconciliation327 — HintChildUpdateAction (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintChildUpdateAction20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintChildToggle20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintToggleGateAction20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintChildUpdateAction_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (CR : CRFamily) (T : Node) (r : T.Seed)
    (node base descriptor gate detBase payBase control Bc colBase workStart sav : ℕ)
    (items : List UpIt) (y : Fin (synLen CR T) → ZMod 2) (i : Fin T.N)
    (hItems : items = hintChildUpdateSchedule CR Bc colBase T node sav)
    (tbl : HintToggleGateTable E descriptor gate i.val detBase payBase control)
    (hArgs : state.regs 6 = descriptor) (hWord : UpWordState E state)
    (hAt : At P base (hintToggleGateAction.compile base)) (hPc : state.pc = base)
    (hLayout : UpSavedLayout E detBase items)
    (hPayEnd : payBase + (sav + 2) ≤ 2 ^ E.W)
    (hGap : wordsOf E.W (synLen CR T) ≤ workStart)
    (h16 : 16 < 2 ^ E.W) (hN : T.N ≤ 2 ^ E.W)
    (hCount : E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length)
    (hPayload : ∀ q < wordsOf E.W (synLen CR T), state.mem (payBase + q) = packMem E.W y q)
    (hLocal : UpLocalTree CR (upShiftDetEnv E detBase) i.val Bc colBase T r node 0 0)
    (hRoom : UpSaveRoom workStart sav T) :
    let z := if state.mem gate = 0 then y else y + hintChildToggleVec CR T r i
    Sem P E base (base + hintToggleGateAction.len) state (fun k out =>
      k ≤ 147 * items.length + 24 ∧ out.regs 14 = control ∧
      (∀ q < wordsOf E.W (synLen CR T), out.mem (payBase + q) = packMem E.W z q) ∧
      UpMemFrame (UpTwoRegion payBase (wordsOf E.W (synLen CR T)) workStart (sav + 2)) state out) := by
  let z := if state.mem gate = 0 then y else y + hintChildToggleVec CR T r i
  let Q := fun m : ℕ → ℕ =>
    (∀ q < wordsOf E.W (synLen CR T), m (payBase + q) = packMem E.W z q) ∧
    (∀ a, ¬ UpTwoRegion payBase (wordsOf E.W (synLen CR T)) workStart (sav + 2) a → m a = state.mem a)
  change Sem P E base (base + hintToggleGateAction.len) state (fun k out =>
    k ≤ 147 * items.length + 10 + 14 ∧ out.regs 14 = control ∧ Q out.mem)
  apply hintToggleGateAction_sem P E state descriptor gate i.val detBase payBase control base
    (147 * items.length + 10) Q tbl hWord hArgs hAt hPc
  · intro hOff
    refine ⟨?_, fun _ _ => rfl⟩
    simpa only [z, if_pos hOff] using hPayload
  · intro hOn st hAtSt hPcSt hMemSt hWordSt h0 h14 h15
    have hRun := hintChildToggle_sem P E CR T r node (base + 10) detBase payBase Bc colBase workStart sav
      items hItems y i st hAtSt hPcSt hLayout hWordSt tbl.payload_fit hPayEnd hGap h16 hN h0 h14 h15 hCount
      (by rw [hMemSt]; exact hPayload) hLocal hRoom
    apply Sem.mono hRun
    rintro k out ⟨hk, hPayloadOut, hFrame, _, h14Out, _, _⟩
    refine ⟨hk, h14Out, ?_, ?_⟩
    · simpa only [z, if_neg hOn] using hPayloadOut
    · intro a hOutside
      exact (hFrame a hOutside).trans (congrFun hMemSt a)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildUpdateAction_sem


