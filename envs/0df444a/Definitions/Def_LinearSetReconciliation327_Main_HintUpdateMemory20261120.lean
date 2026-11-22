-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpdateMemory20261120
-- name    : LinearSetReconciliation327_Main_HintUpdateMemory20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:34:05.12924+00:00
-- url     : https://prove2.me/theorems/d07fb68f-c30b-431b-8cdb-f297d5e67e8b
-- title:
--   LinearSetReconciliation327 — HintUpdateMemory (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpdateMemory20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateArithmetic20261120
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upRegTarget_frame (ins : Instr) (E : RAMEnv) (s : RAMState) (r : Fin 16)
    (h : upRegTarget ins ≠ some r) : (execInstr ins E s).regs r = s.regs r := by
  cases ins <;> simp_all [upRegTarget, execInstr, Function.update_apply, eq_comm]
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upRelativeStore (a v : Fin 16) : List Instr := [.add a 15 a, .store a v]
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upBasedCount : List Instr := [.imm 1 0, .add 1 14 1, .qDet 1 1]
def upBasedNext : List Instr := [.imm 7 16, .mul 7 7 5, .imm 1 8, .add 7 7 1]
theorem upTargets_of_all (code : Program) (r : Fin 16)
    (hCheck : code.all (fun op => decide (upRegTarget op ≠ some r)) = true) :
    ∀ op ∈ code, upRegTarget op ≠ some r := by
  intro op hop
  exact of_decide_eq_true ((List.all_eq_true.mp hCheck) op hop)
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upGuardStoreResult (E : RAMEnv) (s : RAMState) : RAMState :=
  if s.regs 3 = 0 then s else runBlock (upRelativeStore 2 11) E s
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upBasedBodyResult (E : RAMEnv) (a : ℕ) (s : RAMState) : RAMState :=
  let q := runBlock upBasedPrefixCode E s
  runBlock (upBasedNext ++ upBasedCount) E { upGuardStoreResult E q with pc := a + 112 }
attribute [irreducible] upBasedBodyResult
end LinearSetReconciliation327.Main
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upBasedTest : Cond := .lt 4 5 1
def upBasedLoopStep (E : RAMEnv) (head : ℕ) (s : RAMState) : RAMState :=
  let entry : RAMState := { runBlock upBasedTest.code E s with pc := head + 2 }
  { upBasedBodyResult E (head + 2) entry with pc := head }
attribute [irreducible] upBasedLoopStep
def upBasedLoopState (E : RAMEnv) (head : ℕ) (seed : RAMState) : ℕ → RAMState
  | 0 => seed
  | j + 1 => upBasedLoopStep E head (upBasedLoopState E head seed j)
@[simp] theorem upBasedLoopState_zero (E : RAMEnv) (head : ℕ) (seed : RAMState) :
    upBasedLoopState E head seed 0 = seed := rfl
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upSavedMode : List Instr := [.imm 2 6, .sub 2 7 2, .add 2 14 2, .qDet 3 2, .imm 1 2]
def upSavedSlot : List Instr :=
  [.sub 10 7 6, .add 10 14 10, .qDet 10 10, .add 10 15 10, .add 11 10 6, .imm 1 3]
def upSavedWrite : List Instr := [.store 10 8, .store 11 9]
def upSavedRead : List Instr := [.load 8 10, .load 9 11]
def upSavedPost : Stmt :=
  .seq (.code upSavedMode)
    (.ite (.lt 4 3 1) (.code [])
      (.seq (.code upSavedSlot) (.ite (.lt 4 3 1) (.code upSavedWrite) (.code upSavedRead))))
end LinearSetReconciliation327.Main
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upBasedEnd_length : (upBasedNext ++ upBasedCount).length = 7 := rfl
theorem upBasedEnd_noBranch : NoBranch (upBasedNext ++ upBasedCount) := by
  simp [upBasedNext, upBasedCount, NoBranch, Instr.NoBranchI]
theorem upBasedBodyResult_eq (E : RAMEnv) (a : ℕ) (s : RAMState) :
    upBasedBodyResult E a s =
      runBlock (upBasedNext ++ upBasedCount) E
        { upGuardStoreResult E (runBlock upBasedPrefixCode E s) with pc := a + 112 } := by unfold upBasedBodyResult <;> rfl
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upBlock_register_frame (code : List Instr) (E : RAMEnv) (s : RAMState) (r : Fin 16)
    (h : ∀ op ∈ code, upRegTarget op ≠ some r) : (runBlock code E s).regs r = s.regs r := by
  induction code generalizing s with
  | nil => rfl
  | cons ins rest ih =>
      rw [runBlock_cons, ih (execInstr ins E s) (fun op ho => h op (by simp [ho]))]
      exact upRegTarget_frame ins E s r (h ins (by simp))
theorem upBasedCount_spec (E : RAMEnv) (s : RAMState) :
    (runBlock upBasedCount E s).regs 1 = E.det (s.regs 14 % 2 ^ E.W) % 2 ^ E.W := by
  simp [upBasedCount, runBlock, execInstr, Function.update_apply]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
theorem upBasedRest_targets (r : Fin 16) (hr : r = 0 ∨ r = 5 ∨ r = 6 ∨ r = 14 ∨ r = 15) :
    ∀ op ∈ (upBasedCore ++ (upBasedWidth ++ upBasedRead)), upRegTarget op ≠ some r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> apply upTargets_of_all <;> decide
theorem upBasedPrefix_meta (E : RAMEnv) (s : RAMState) :
    (upBasedPrefixRun E s).regs 5 = (s.regs 5 + s.regs 6) % 2 ^ E.W ∧
      (∀ r, r = 0 ∨ r = 6 ∨ r = 14 ∨ r = 15 → (upBasedPrefixRun E s).regs r = s.regs r) := by
  have hState : runBlock upBasedPrefixCode E s =
      runBlock (upBasedCore ++ (upBasedWidth ++ upBasedRead)) E (execInstr (.add 5 5 6) E s) := by
    simp only [upBasedPrefixCode, runBlock_append, runBlock_cons, runBlock_nil]
  rw [upBasedPrefixRun_eq, hState]
  constructor
  · rw [upBlock_register_frame _ E _ 5 (upBasedRest_targets 5 (Or.inr (Or.inl rfl)))]
    rfl
  · intro r hr
    have hIn : r = 0 ∨ r = 5 ∨ r = 6 ∨ r = 14 ∨ r = 15 := by tauto
    rw [upBlock_register_frame _ E _ r (upBasedRest_targets r hIn)]
    rcases hr with rfl | rfl | rfl | rfl <;> rfl
theorem upGuardStore_register_frame (E : RAMEnv) (s : RAMState) (r : Fin 16) (hr : r ≠ 2) :
    (upGuardStoreResult E s).regs r = s.regs r := by
  by_cases hz : s.regs 3 = 0
  · simp only [upGuardStoreResult, if_pos hz]
  · simp [upGuardStoreResult, hz, upRelativeStore, runBlock, execInstr, Function.update_apply, hr]
theorem upBasedEnd_targets (r : Fin 16) (hr : r ≠ 1) (hr' : r ≠ 7) :
    ∀ op ∈ (upBasedNext ++ upBasedCount), upRegTarget op ≠ some r := by
  simp [upBasedNext, upBasedCount, upRegTarget, Ne.symm hr, Ne.symm hr']
theorem upBasedBodyResult_meta (E : RAMEnv) (a : ℕ) (s : RAMState) :
    (upBasedBodyResult E a s).pc = a + 119 ∧
      (upBasedBodyResult E a s).regs 5 = (s.regs 5 + s.regs 6) % 2 ^ E.W ∧
      (upBasedBodyResult E a s).regs 1 = E.det (s.regs 14 % 2 ^ E.W) % 2 ^ E.W ∧
      (∀ r, r = 0 ∨ r = 6 ∨ r = 14 ∨ r = 15 → (upBasedBodyResult E a s).regs r = s.regs r) := by
  let q := upBasedPrefixRun E s
  let u : RAMState := { upGuardStoreResult E q with pc := a + 112 }
  have hQ := upBasedPrefix_meta E s
  have hEq : upBasedBodyResult E a s = runBlock (upBasedNext ++ upBasedCount) E u := by
    rw [upBasedBodyResult_eq, ← upBasedPrefixRun_eq]
  have hFr : ∀ r, r ≠ 1 → r ≠ 2 → r ≠ 7 →
      (runBlock (upBasedNext ++ upBasedCount) E u).regs r = q.regs r := by
    intro r h1 h2 h7
    exact (upBlock_register_frame _ E u r (upBasedEnd_targets r h1 h7)).trans
      (upGuardStore_register_frame E q r h2)
  have hBase : (runBlock upBasedNext E u).regs 14 = s.regs 14 := by
    have hN : (runBlock upBasedNext E u).regs 14 = u.regs 14 :=
      upBlock_register_frame _ E u 14 (by simp [upBasedNext, upRegTarget])
    exact hN.trans ((upGuardStore_register_frame E q 14 (by decide)).trans
      (hQ.2 14 (Or.inr (Or.inr (Or.inl rfl)))))
  rw [hEq]
  refine ⟨?_, (hFr 5 (by decide) (by decide) (by decide)).trans hQ.1, ?_, ?_⟩
  · rw [runBlock_pc _ E u upBasedEnd_noBranch, upBasedEnd_length]
  · rw [runBlock_append, upBasedCount_spec, hBase]
  · intro r hr
    have h1 : r ≠ 1 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ 2 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h7 : r ≠ 7 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    exact (hFr r h1 h2 h7).trans (hQ.2 r hr)
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upFiniteEval (E : RAMEnv) : Stmt → RAMState → RAMState
  | .code code, s => runBlock code E s
  | .seq left right, s => upFiniteEval E right (upFiniteEval E left s)
  | .ite c left right, s =>
      let tested := runBlock c.code E s
      if tested.regs c.test = 0 then upFiniteEval E right tested else upFiniteEval E left tested
  | .loop _ _, s => s
end LinearSetReconciliation327.Main
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upSavedPostRun (E : RAMEnv) (p : RAMState) : RAMState := upFiniteEval E upSavedPost p
attribute [irreducible] upSavedPostRun
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upSavedBodyResult (E : RAMEnv) (base : ℕ) (p : RAMState) : RAMState :=
  runBlock upBasedCount E { upSavedPostRun E (upBasedBodyResult E base p) with pc := base + 142 }
theorem upSavedBodyResult_eq (E : RAMEnv) (base : ℕ) (p : RAMState) :
    upSavedBodyResult E base p =
      runBlock upBasedCount E { upSavedPostRun E (upBasedBodyResult E base p) with pc := base + 142 } := by unfold upSavedBodyResult <;> rfl
attribute [irreducible] upSavedBodyResult
end LinearSetReconciliation327.Main
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upWord_sub_small (M a b : ℕ) (ha : a < M) (hb : b ≤ a) :
    (a + M - b) % M = a - b := by
  rw [show a + M - b = (a - b) + M from by omega]
  simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt ((Nat.sub_le a b).trans_lt ha)
theorem upSavedMode_spec (E : RAMEnv) (p : RAMState) (ptr betaDet mode : ℕ)
    (h7 : p.regs 7 = ptr + 16) (h14 : p.regs 14 = betaDet)
    (h16 : ptr + 16 < 2 ^ E.W)
    (hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = mode) :
    let out := runBlock upSavedMode E p
    out.pc = p.pc + 5 ∧ out.mem = p.mem ∧ out.regs 3 = mode ∧ out.regs 1 = 2 ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → out.regs r = p.regs r) := by
  have hSix : 6 < 2 ^ E.W := by omega
  have h2 : 2 < 2 ^ E.W := by omega
  have hSub : (ptr + 16 + 2 ^ E.W - 6) % 2 ^ E.W = ptr + 10 := by
    rw [upWord_sub_small _ _ _ h16 (by omega)]
    omega
  dsimp only
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [upSavedMode, runBlock, execInstr, Nat.add_assoc]
  · simp [upSavedMode, runBlock, execInstr, Function.update_apply, h7, h14,
      Nat.mod_eq_of_lt hSix, hSub, hMode]
  · simp [upSavedMode, runBlock, execInstr, Function.update_apply, Nat.mod_eq_of_lt h2]
  · intro r hr1 hr2 hr3
    simp [upSavedMode, runBlock, execInstr, Function.update_apply, hr1, hr2, hr3]
theorem upSavedSlot_spec (E : RAMEnv) (p : RAMState) (ptr betaDet betaPay sav : ℕ)
    (h7 : p.regs 7 = ptr + 16) (h6 : p.regs 6 = 1)
    (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay)
    (h16 : ptr + 16 < 2 ^ E.W)
    (hSav : E.det ((betaDet + (ptr + 15)) % 2 ^ E.W) % 2 ^ E.W = sav) :
    let out := runBlock upSavedSlot E p
    out.pc = p.pc + 6 ∧ out.mem = p.mem ∧
      out.regs 10 = (betaPay + sav) % 2 ^ E.W ∧
      out.regs 11 = (betaPay + (sav + 1)) % 2 ^ E.W ∧ out.regs 1 = 3 ∧
      (∀ r, r ≠ 1 → r ≠ 10 → r ≠ 11 → out.regs r = p.regs r) := by
  have h3 : 3 < 2 ^ E.W := by omega
  have h1 : 1 < 2 ^ E.W := by omega
  have hSub : (ptr + 16 + 2 ^ E.W - 1) % 2 ^ E.W = ptr + 15 := by
    rw [upWord_sub_small _ _ _ h16 (by omega)]
    omega
  have hAdd : ((betaPay + sav) % 2 ^ E.W + 1) % 2 ^ E.W = (betaPay + (sav + 1)) % 2 ^ E.W := by
    rw [← Nat.add_assoc, Nat.add_mod ((betaPay + sav) % 2 ^ E.W) 1 (2 ^ E.W),
      Nat.mod_mod, Nat.add_mod (betaPay + sav) 1 (2 ^ E.W)]
  dsimp only
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [upSavedSlot, runBlock, execInstr, Nat.add_assoc]
  · simp [upSavedSlot, runBlock, execInstr, Function.update_apply, h7, h6, h14, h15, hSub, hSav]
  · simpa [upSavedSlot, runBlock, execInstr, Function.update_apply, h7, h6, h14, h15, hSub, hSav] using hAdd
  · simp [upSavedSlot, runBlock, execInstr, Function.update_apply, Nat.mod_eq_of_lt h3]
  · intro r hr1 hr10 hr11
    simp [upSavedSlot, runBlock, execInstr, Function.update_apply, hr1, hr10, hr11]
theorem upSavedWrite_spec (E : RAMEnv) (p : RAMState) :
    let out := runBlock upSavedWrite E p
    out.pc = p.pc + 2 ∧ out.regs = p.regs ∧
      out.mem = Function.update (Function.update p.mem (p.regs 10) (p.regs 8)) (p.regs 11) (p.regs 9) := by
  refine ⟨?_, rfl, rfl⟩
  simp [upSavedWrite, runBlock, execInstr, Nat.add_assoc]
theorem upSavedRead_spec (E : RAMEnv) (p : RAMState) :
    let out := runBlock upSavedRead E p
    out.pc = p.pc + 2 ∧ out.mem = p.mem ∧
      out.regs 8 = p.mem (p.regs 10) % 2 ^ E.W ∧
      out.regs 9 = p.mem (p.regs 11) % 2 ^ E.W ∧
      (∀ r, r ≠ 8 → r ≠ 9 → out.regs r = p.regs r) := by
  dsimp only
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [upSavedRead, runBlock, execInstr, Nat.add_assoc]
  · simp [upSavedRead, runBlock, execInstr, Function.update_apply]
  · simp [upSavedRead, runBlock, execInstr, Function.update_apply]
  · intro r hr8 hr9
    simp [upSavedRead, runBlock, execInstr, Function.update_apply, hr8, hr9]
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upSavedCmp : Cond := .lt 4 3 1
theorem upSavedCmp_frame (E : RAMEnv) (p : RAMState) (r : Fin 16) (hr : r ≠ 4) :
    (runBlock upSavedCmp.code E p).regs r = p.regs r := by
  simp [upSavedCmp, Cond.code, runBlock, execInstr, Function.update_apply, hr]
theorem upSavedCmp_mem (E : RAMEnv) (p : RAMState) :
    (runBlock upSavedCmp.code E p).mem = p.mem := rfl
theorem upSavedCmp_value (E : RAMEnv) (p : RAMState) (hWord : 1 < 2 ^ E.W) :
    (runBlock upSavedCmp.code E p).regs 4 = if p.regs 3 < p.regs 1 then 1 else 0 := by
  simp only [upSavedCmp, Cond.code, runBlock_cons, runBlock_nil, execInstr]
  by_cases h : p.regs 3 < p.regs 1 <;> simp [h, Nat.mod_eq_of_lt hWord]
def upSavedPrepRun (E : RAMEnv) (p : RAMState) : RAMState :=
  runBlock upSavedCmp.code E (runBlock upSavedSlot E
    (runBlock upSavedCmp.code E (runBlock upSavedMode E p)))
theorem upSavedPrepRun_eq (E : RAMEnv) (p : RAMState) :
    upSavedPrepRun E p = runBlock upSavedCmp.code E (runBlock upSavedSlot E
      (runBlock upSavedCmp.code E (runBlock upSavedMode E p))) := by unfold upSavedPrepRun <;> rfl
attribute [irreducible] upSavedPrepRun
theorem upSavedPostRun_branch (E : RAMEnv) (p : RAMState) :
    upSavedPostRun E p =
      if (runBlock upSavedCmp.code E (runBlock upSavedMode E p)).regs 4 = 0 then
        if (upSavedPrepRun E p).regs 4 = 0 then runBlock upSavedRead E (upSavedPrepRun E p)
        else runBlock upSavedWrite E (upSavedPrepRun E p)
      else runBlock upSavedCmp.code E (runBlock upSavedMode E p) := by
  unfold upSavedPostRun upSavedPrepRun
  simp only [upSavedPost, upFiniteEval, upSavedCmp, Cond.test, runBlock_nil]
  all_goals (delta upFiniteEval; rfl)
structure UpSavedPrepared (E : RAMEnv) (betaPay mode sav : ℕ) (p q : RAMState) : Prop where
  mem : q.mem = p.mem
  coord : q.regs 8 = p.regs 8
  flag : q.regs 9 = p.regs 9
  first : q.regs 10 = (betaPay + sav) % 2 ^ E.W
  second : q.regs 11 = (betaPay + (sav + 1)) % 2 ^ E.W
  mode_eq : q.regs 3 = mode
  limit : q.regs 1 = 3
  test : q.regs 4 = if mode < 3 then 1 else 0
theorem upSavedPost_prepare (E : RAMEnv) (p : RAMState) (ptr betaDet betaPay mode sav : ℕ)
    (h7 : p.regs 7 = ptr + 16) (h6 : p.regs 6 = 1)
    (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay) (h16 : ptr + 16 < 2 ^ E.W)
    (hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = mode)
    (hSav : E.det ((betaDet + (ptr + 15)) % 2 ^ E.W) % 2 ^ E.W = sav) :
    UpSavedPrepared E betaPay mode sav p (upSavedPrepRun E p) := by
  let q := runBlock upSavedMode E p
  let t := runBlock upSavedCmp.code E q
  let u := runBlock upSavedSlot E t
  have hWord : 1 < 2 ^ E.W := by omega
  have hM := upSavedMode_spec E p ptr betaDet mode h7 h14 h16 hMode
  have hT : ∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → t.regs r = p.regs r := by
    intro r h1 h2 h3 h4
    exact (upSavedCmp_frame E q r h4).trans (hM.2.2.2.2 r h1 h2 h3)
  have hS := upSavedSlot_spec E t ptr betaDet betaPay sav
    ((hT 7 (by decide) (by decide) (by decide) (by decide)).trans h7)
    ((hT 6 (by decide) (by decide) (by decide) (by decide)).trans h6)
    ((hT 14 (by decide) (by decide) (by decide) (by decide)).trans h14)
    ((hT 15 (by decide) (by decide) (by decide) (by decide)).trans h15) h16 hSav
  have hModeU : u.regs 3 = mode :=
    (hS.2.2.2.2.2 3 (by decide) (by decide) (by decide)).trans
      ((upSavedCmp_frame E q 3 (by decide)).trans hM.2.2.1)
  have hLimit : u.regs 1 = 3 := hS.2.2.2.2.1
  have hMemU : u.mem = p.mem := hS.2.1.trans ((upSavedCmp_mem E q).trans hM.2.1)
  rw [upSavedPrepRun_eq]
  refine ⟨(upSavedCmp_mem E u).trans hMemU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (upSavedCmp_frame E u 8 (by decide)).trans
      ((hS.2.2.2.2.2 8 (by decide) (by decide) (by decide)).trans (hT 8 (by decide) (by decide) (by decide) (by decide)))
  · exact (upSavedCmp_frame E u 9 (by decide)).trans
      ((hS.2.2.2.2.2 9 (by decide) (by decide) (by decide)).trans (hT 9 (by decide) (by decide) (by decide) (by decide)))
  · exact (upSavedCmp_frame E u 10 (by decide)).trans hS.2.2.1
  · exact (upSavedCmp_frame E u 11 (by decide)).trans hS.2.2.2.1
  · exact (upSavedCmp_frame E u 3 (by decide)).trans hModeU
  · exact (upSavedCmp_frame E u 1 (by decide)).trans hLimit
  · rw [upSavedCmp_value E u hWord, hModeU, hLimit]
theorem upSavedPost_high_branch (E : RAMEnv) (p : RAMState) (ptr betaDet mode : ℕ)
    (h7 : p.regs 7 = ptr + 16) (h14 : p.regs 14 = betaDet) (h16 : ptr + 16 < 2 ^ E.W)
    (hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = mode) (hHigh : 2 ≤ mode) :
    upSavedPostRun E p =
      if (upSavedPrepRun E p).regs 4 = 0 then runBlock upSavedRead E (upSavedPrepRun E p)
      else runBlock upSavedWrite E (upSavedPrepRun E p) := by
  have hM := upSavedMode_spec E p ptr betaDet mode h7 h14 h16 hMode
  have hZero : (runBlock upSavedCmp.code E (runBlock upSavedMode E p)).regs 4 = 0 := by
    rw [upSavedCmp_value E _ (by omega), hM.2.2.1, hM.2.2.2.1, if_neg (by omega)]
  rw [upSavedPostRun_branch, if_pos hZero]
theorem upSavedPost_normal (E : RAMEnv) (p : RAMState) (ptr betaDet mode : ℕ)
    (h7 : p.regs 7 = ptr + 16) (h14 : p.regs 14 = betaDet) (h16 : ptr + 16 < 2 ^ E.W)
    (hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = mode) (hLow : mode < 2) :
    (upSavedPostRun E p).mem = p.mem ∧
      (upSavedPostRun E p).regs 8 = p.regs 8 ∧ (upSavedPostRun E p).regs 9 = p.regs 9 := by
  let q := runBlock upSavedMode E p
  have hM := upSavedMode_spec E p ptr betaDet mode h7 h14 h16 hMode
  have hNZ : (runBlock upSavedCmp.code E (runBlock upSavedMode E p)).regs 4 ≠ 0 := by
    rw [upSavedCmp_value E _ (by omega), hM.2.2.1, hM.2.2.2.1, if_pos hLow]
    decide
  have hRun : upSavedPostRun E p = runBlock upSavedCmp.code E q := by
    rw [upSavedPostRun_branch, if_neg hNZ]
  simp only [hRun]
  exact ⟨(upSavedCmp_mem E q).trans hM.2.1,
    (upSavedCmp_frame E q 8 (by decide)).trans (hM.2.2.2.2 8 (by decide) (by decide) (by decide)),
    (upSavedCmp_frame E q 9 (by decide)).trans (hM.2.2.2.2 9 (by decide) (by decide) (by decide))⟩
theorem upSavedPost_save (E : RAMEnv) (p : RAMState) (ptr betaDet betaPay sav : ℕ)
    (h7 : p.regs 7 = ptr + 16) (h6 : p.regs 6 = 1)
    (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay) (h16 : ptr + 16 < 2 ^ E.W)
    (hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = 2)
    (hSav : E.det ((betaDet + (ptr + 15)) % 2 ^ E.W) % 2 ^ E.W = sav) :
    (upSavedPostRun E p).mem = Function.update
      (Function.update p.mem ((betaPay + sav) % 2 ^ E.W) (p.regs 8))
      ((betaPay + (sav + 1)) % 2 ^ E.W) (p.regs 9) ∧
      (upSavedPostRun E p).regs 8 = p.regs 8 ∧ (upSavedPostRun E p).regs 9 = p.regs 9 := by
  have hPrep := upSavedPost_prepare E p ptr betaDet betaPay 2 sav h7 h6 h14 h15 h16 hMode hSav
  have hNZ : (upSavedPrepRun E p).regs 4 ≠ 0 := by rw [hPrep.test]; decide
  have hRun : upSavedPostRun E p = runBlock upSavedWrite E (upSavedPrepRun E p) := by
    rw [upSavedPost_high_branch E p ptr betaDet 2 h7 h14 h16 hMode (by decide), if_neg hNZ]
  simp only [hRun]
  have hW := upSavedWrite_spec E (upSavedPrepRun E p)
  refine ⟨?_, ?_, ?_⟩
  · rw [hW.2.2, hPrep.mem, hPrep.first, hPrep.second, hPrep.coord, hPrep.flag]
  · exact (congrFun hW.2.1 8).trans hPrep.coord
  · exact (congrFun hW.2.1 9).trans hPrep.flag
theorem upSavedPost_restore (E : RAMEnv) (p : RAMState) (ptr betaDet betaPay sav : ℕ)
    (h7 : p.regs 7 = ptr + 16) (h6 : p.regs 6 = 1)
    (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay) (h16 : ptr + 16 < 2 ^ E.W)
    (hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = 3)
    (hSav : E.det ((betaDet + (ptr + 15)) % 2 ^ E.W) % 2 ^ E.W = sav) :
    (upSavedPostRun E p).mem = p.mem ∧
      (upSavedPostRun E p).regs 8 = p.mem ((betaPay + sav) % 2 ^ E.W) % 2 ^ E.W ∧
      (upSavedPostRun E p).regs 9 = p.mem ((betaPay + (sav + 1)) % 2 ^ E.W) % 2 ^ E.W := by
  have hPrep := upSavedPost_prepare E p ptr betaDet betaPay 3 sav h7 h6 h14 h15 h16 hMode hSav
  have hZ : (upSavedPrepRun E p).regs 4 = 0 := by rw [hPrep.test]; rfl
  have hRun : upSavedPostRun E p = runBlock upSavedRead E (upSavedPrepRun E p) := by
    rw [upSavedPost_high_branch E p ptr betaDet 3 h7 h14 h16 hMode (by decide), if_pos hZ]
  simp only [hRun]
  have hR := upSavedRead_spec E (upSavedPrepRun E p)
  refine ⟨hR.2.1.trans hPrep.mem, ?_, ?_⟩
  · rw [hR.2.2.1, hPrep.mem, hPrep.first]
  · rw [hR.2.2.2.1, hPrep.mem, hPrep.second]
end LinearSetReconciliation327.Main
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upCyclicAddr_inj (W beta a b : ℕ)
    (hBeta : beta < 2 ^ W) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    upCyclicAddr W beta a = upCyclicAddr W beta b ↔ a = b := by
  have hmod : ∀ x, x < 2 ^ W → (beta + x) % 2 ^ W =
      if beta + x < 2 ^ W then beta + x else beta + x - 2 ^ W := by
    intro x hx
    by_cases hs : beta + x < 2 ^ W
    · rw [if_pos hs, Nat.mod_eq_of_lt hs]
    · rw [if_neg hs]
      have hsplit : beta + x = 2 ^ W + (beta + x - 2 ^ W) := by omega
      have hr : beta + x - 2 ^ W < 2 ^ W := by omega
      calc
        (beta + x) % 2 ^ W = (2 ^ W + (beta + x - 2 ^ W)) % 2 ^ W := congrArg (· % 2 ^ W) hsplit
        _ = (beta + x - 2 ^ W) % 2 ^ W := by simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
        _ = beta + x - 2 ^ W := Nat.mod_eq_of_lt hr
  constructor
  · intro h
    change (beta + a) % 2 ^ W = (beta + b) % 2 ^ W at h
    rw [hmod a ha, hmod b hb] at h
    split_ifs at h <;> omega
  · rintro rfl; rfl
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upVirtualMem_update (W beta wi value : ℕ) (mem : ℕ → ℕ)
    (hBeta : beta < 2 ^ W) (hWi : wi < 2 ^ W) :
    upVirtualMem W beta (Function.update mem (upCyclicAddr W beta wi) value) =
      Function.update (upVirtualMem W beta mem) wi (value % 2 ^ W) := by
  funext q
  by_cases hq : q < 2 ^ W
  · have heq := upCyclicAddr_inj W beta q wi hBeta hq hWi
    simp only [upVirtualMem, if_pos hq, Function.update_apply, heq]
    by_cases he : q = wi <;> simp [he]
  · have hne : q ≠ wi := by omega
    simp [upVirtualMem, hq, Function.update_apply, hne]
end LinearSetReconciliation327.Main
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upVirtualMem_lt (W beta : ℕ) (mem : ℕ → ℕ) (a : ℕ) :
    upVirtualMem W beta mem a < 2 ^ W := by
  unfold upVirtualMem
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos W)
  · exact Nat.two_pow_pos W
theorem upGuardStore_virtual (E : RAMEnv) (p : RAMState) (beta wi mask : ℕ)
    (hBase : p.regs 15 = beta) (hWi : p.regs 2 = wi) (hMask : p.regs 3 = mask)
    (hBeta : beta < 2 ^ E.W) (hWiBound : wi < 2 ^ E.W)
    (hNew : p.regs 11 = ((upVirtualMem E.W beta p.mem wi) ^^^ mask) % 2 ^ E.W) :
    upVirtualMem E.W beta (upGuardStoreResult E p).mem =
      Function.update (upVirtualMem E.W beta p.mem) wi
        (((upVirtualMem E.W beta p.mem wi) ^^^ mask) % 2 ^ E.W) := by
  by_cases hz : mask = 0
  · have hWord := upVirtualMem_lt E.W beta p.mem wi
    rw [upGuardStoreResult, if_pos (hMask.trans hz)]
    simp only [hz, Nat.xor_zero, Nat.mod_eq_of_lt hWord]
    funext q
    by_cases hq : q = wi <;> simp [Function.update_apply, hq]
  · have hNZ : p.regs 3 ≠ 0 := by simpa [hMask] using hz
    have hMem : (upGuardStoreResult E p).mem =
        Function.update p.mem (upCyclicAddr E.W beta wi) (p.regs 11) := by
      simp [upGuardStoreResult, hNZ, upRelativeStore, runBlock, execInstr,
        Function.update_apply, hBase, hWi, upCyclicAddr]
    rw [hMem, upVirtualMem_update E.W beta wi _ p.mem hBeta hWiBound, hNew, Nat.mod_mod]
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def upApplyBody (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) : UpAbs :=
  { mem := Function.update a.mem (upvWi E i it a) (upvNew E i it a)
    c := upvCn E i it a
    f := upvFn E i it a }
def upvG2 (E : RAMEnv) (it : UpIt) : ℕ := (if it.mode < 2 then 1 else 0) % 2 ^ E.W
def upvG3 (E : RAMEnv) (it : UpIt) : ℕ := (if it.mode < 3 then 1 else 0) % 2 ^ E.W
def upvA2 (E : RAMEnv) (it : UpIt) : ℕ := (1 % 2 ^ E.W + 2 ^ E.W - upvG2 E it) % 2 ^ E.W
def upvA3 (E : RAMEnv) (it : UpIt) : ℕ := (1 % 2 ^ E.W + 2 ^ E.W - upvG3 E it) % 2 ^ E.W
def upvRt (E : RAMEnv) (it : UpIt) : ℕ := it.setSt * upvA3 E it % 2 ^ E.W
def upvSv (E : RAMEnv) (it : UpIt) : ℕ := (upvA2 E it + 2 ^ E.W - upvRt E it) % 2 ^ E.W
def upvM0 (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) : ℕ :=
  (upApplyBody E i it a).mem it.sav % 2 ^ E.W
def upvM1 (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) : ℕ :=
  (upApplyBody E i it a).mem (it.sav + 1) % 2 ^ E.W
def upvCnf (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) : ℕ :=
  (upvCn E i it a
    + (upvM0 E i it a + 2 ^ E.W - upvCn E i it a) % 2 ^ E.W * upvRt E it % 2 ^ E.W)
    % 2 ^ E.W
def upvFnf (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) : ℕ :=
  (upvFn E i it a
    + (upvM1 E i it a + 2 ^ E.W - upvFn E i it a) % 2 ^ E.W * upvRt E it % 2 ^ E.W)
    % 2 ^ E.W
def upvV0 (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) : ℕ :=
  ((upvCnf E i it a + 2 ^ E.W - upvM0 E i it a) % 2 ^ E.W * upvSv E it % 2 ^ E.W
    + upvM0 E i it a) % 2 ^ E.W
def upvV1 (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) : ℕ :=
  ((upvFnf E i it a + 2 ^ E.W - upvM1 E i it a) % 2 ^ E.W * upvSv E it % 2 ^ E.W
    + upvM1 E i it a) % 2 ^ E.W
def upApply (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) : UpAbs :=
  { mem := Function.update
      (Function.update (upApplyBody E i it a).mem it.sav (upvV0 E i it a))
      (it.sav + 1) (upvV1 E i it a)
    c := upvCnf E i it a
    f := upvFnf E i it a }
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upBasedEnd_mem (E : RAMEnv) (p : RAMState) :
    (runBlock (upBasedNext ++ upBasedCount) E p).mem = p.mem := rfl
theorem upBasedBodyResult_mem (E : RAMEnv) (a : ℕ) (p : RAMState) :
    (upBasedBodyResult E a p).mem = (upGuardStoreResult E (upBasedPrefixRun E p)).mem := by
  rw [upBasedBodyResult_eq, ← upBasedPrefixRun_eq]
  exact upBasedEnd_mem E _
theorem upBasedBodyResult_data_frame (E : RAMEnv) (a : ℕ) (p : RAMState) (r : Fin 16)
    (h1 : r ≠ 1) (h2 : r ≠ 2) (h7 : r ≠ 7) :
    (upBasedBodyResult E a p).regs r = (upBasedPrefixRun E p).regs r := by
  rw [upBasedBodyResult_eq, ← upBasedPrefixRun_eq]
  exact (upBlock_register_frame _ E _ r (upBasedEnd_targets r h1 h7)).trans
    (upGuardStore_register_frame E _ r h2)
theorem upBasedView_bound (W beta : ℕ) (ab : UpAbs) (p : RAMState)
    (hView : UpBasedView W beta ab p) : ∀ q, ab.mem q < 2 ^ W := by
  intro q
  have hh := upVirtualMem_lt W beta p.mem q
  rw [hView.mem] at hh
  exact hh
theorem upBasedBody_view_of_data (E : RAMEnv) (a betaDet betaPay i : ℕ)
    (it : UpIt) (ab : UpAbs) (p : RAMState)
    (hView : UpBasedView E.W betaPay ab p) (hPay : betaPay < 2 ^ E.W)
    (hData : UpBasedPrefixData E betaDet betaPay i it ab p (upBasedPrefixRun E p)) :
    UpBasedView E.W betaPay (upApplyBody (upShiftDetEnv E betaDet) i it ab)
      (upBasedBodyResult E a p) := by
  let F := upShiftDetEnv E betaDet
  let q := upBasedPrefixRun E p
  let wi := upvWi F i it ab
  let mask := upvMask F i it ab
  have hBound := upBasedView_bound E.W betaPay ab p hView
  have hNorm : upVirtualMem E.W betaPay q.mem = ab.mem := by rw [hData.mem]; exact hView.mem
  have hWi : wi < 2 ^ E.W := Nat.mod_lt _ (Nat.two_pow_pos E.W)
  have hNew : upvNew F i it ab = ((ab.mem wi) ^^^ mask) % 2 ^ E.W := by
    change ((ab.mem wi % 2 ^ E.W) ^^^ mask) % 2 ^ E.W = _
    rw [Nat.mod_eq_of_lt (hBound wi)]
  have hQnew : q.regs 11 = ((upVirtualMem E.W betaPay q.mem wi) ^^^ mask) % 2 ^ E.W := by
    rw [hData.value, hNorm]
    exact hNew
  have hVirtual := upGuardStore_virtual E q betaPay wi mask hData.pay hData.word hData.mask hPay hWi hQnew
  rw [hNorm, ← hNew] at hVirtual
  refine ⟨?_, ?_, ?_⟩
  · rw [upBasedBodyResult_mem]
    exact hVirtual
  · exact (upBasedBodyResult_data_frame E a p 8 (by decide) (by decide) (by decide)).trans hData.coord
  · exact (upBasedBodyResult_data_frame E a p 9 (by decide) (by decide) (by decide)).trans hData.flag
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def upSave (sav : ℕ) : UpIt := { mode := 2, sav := sav }
def upRestore (sav : ℕ) : UpIt := { setSt := 1, mode := 3, sav := sav }
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def UpItemKind (it : UpIt) : Prop :=
  it.mode < 2 ∨ ∃ sav, it = upSave sav ∨ it = upRestore sav
theorem upSavedBodyResult_data (E : RAMEnv) (base : ℕ) (p : RAMState) :
    (upSavedBodyResult E base p).mem = (upSavedPostRun E (upBasedBodyResult E base p)).mem ∧
      (upSavedBodyResult E base p).regs 8 = (upSavedPostRun E (upBasedBodyResult E base p)).regs 8 ∧
      (upSavedBodyResult E base p).regs 9 = (upSavedPostRun E (upBasedBodyResult E base p)).regs 9 := by
  rw [upSavedBodyResult_eq]
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · exact upBlock_register_frame upBasedCount E _ 8 (by simp [upBasedCount, upRegTarget])
  · exact upBlock_register_frame upBasedCount E _ 9 (by simp [upBasedCount, upRegTarget])
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def UpBasedRawPayload (beta words : ℕ) (ab : UpAbs) (p : RAMState) : Prop :=
  ∀ q, q < words → p.mem (beta + q) = ab.mem q
theorem upBasedRaw_update (W beta words wi value : ℕ) (mem old : ℕ → ℕ)
    (hBeta : beta < 2 ^ W) (hEnd : beta + words ≤ 2 ^ W) (hWi : wi < 2 ^ W)
    (hOld : ∀ q, q < words → mem (beta + q) = old q) :
    ∀ q, q < words →
      Function.update mem (upCyclicAddr W beta wi) value (beta + q) =
        Function.update old wi value q := by
  intro q hq
  have hQ : q < 2 ^ W := by omega
  have hAddr : beta + q < 2 ^ W := by omega
  have hEq : (beta + q = upCyclicAddr W beta wi) ↔ q = wi := by
    simpa only [upCyclicAddr, Nat.mod_eq_of_lt hAddr] using upCyclicAddr_inj W beta q wi hBeta hQ hWi
  simp only [Function.update_apply, hEq]
  by_cases he : q = wi <;> simp [he, hOld q hq]
theorem upGuardStore_mem_nonzero (E : RAMEnv) (p : RAMState) (hNZ : p.regs 3 ≠ 0) :
    (upGuardStoreResult E p).mem = Function.update p.mem ((p.regs 15 + p.regs 2) % 2 ^ E.W) (p.regs 11) := by
  simp [upGuardStoreResult, hNZ, upRelativeStore, runBlock, execInstr, Function.update_apply]
theorem upBasedBody_raw_of_data (E : RAMEnv) (a betaDet betaPay i words : ℕ)
    (it : UpIt) (ab : UpAbs) (p : RAMState)
    (hView : UpBasedView E.W betaPay ab p) (hRaw : UpBasedRawPayload betaPay words ab p)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + words ≤ 2 ^ E.W)
    (hData : UpBasedPrefixData E betaDet betaPay i it ab p (upBasedPrefixRun E p)) :
    UpBasedRawPayload betaPay words (upApplyBody (upShiftDetEnv E betaDet) i it ab)
      (upBasedBodyResult E a p) := by
  let F := upShiftDetEnv E betaDet
  let wi := upvWi F i it ab
  have hWi : wi < 2 ^ E.W := Nat.mod_lt _ (Nat.two_pow_pos E.W)
  have hBound := upBasedView_bound E.W betaPay ab p hView
  intro q hq
  rw [upBasedBodyResult_mem]
  by_cases hz : upvMask F i it ab = 0
  · have hNZ : (upBasedPrefixRun E p).regs 3 = 0 := hData.mask.trans hz
    rw [upGuardStoreResult, if_pos hNZ, hData.mem]
    have hNew : upvNew F i it ab = ab.mem wi := by
      change ((ab.mem wi % 2 ^ E.W) ^^^ upvMask F i it ab) % 2 ^ E.W = _
      rw [hz, Nat.xor_zero, Nat.mod_mod, Nat.mod_eq_of_lt (hBound wi)]
    change p.mem (betaPay + q) = Function.update ab.mem wi (upvNew F i it ab) q
    rw [hNew]
    have hSelf : Function.update ab.mem wi (ab.mem wi) = ab.mem := by
      funext j
      by_cases hj : j = wi <;> simp [Function.update_apply, hj]
    rw [hSelf]
    exact hRaw q hq
  · have hNZ : (upBasedPrefixRun E p).regs 3 ≠ 0 := by rw [hData.mask]; exact hz
    rw [upGuardStore_mem_nonzero E _ hNZ, hData.pay, hData.word, hData.value, hData.mem]
    exact upBasedRaw_update E.W betaPay words wi (upvNew F i it ab) p.mem ab.mem hPay hEnd hWi hRaw q hq
theorem upBasedRaw_initial (W beta words : ℕ) (ab : UpAbs) (p : RAMState)
    (hView : UpBasedView W beta ab p) (hEnd : beta + words ≤ 2 ^ W)
    (hBound : ∀ q, q < words → p.mem (beta + q) < 2 ^ W) : UpBasedRawPayload beta words ab p := by
  intro q hq
  have hQ : q < 2 ^ W := by omega
  have hAddr : beta + q < 2 ^ W := by omega
  rw [← hView.mem]
  simp only [upVirtualMem, if_pos hQ, upCyclicAddr,
    Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt (hBound q hq)]
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upRelativeStore_spec (E : RAMEnv) (s : RAMState) (a v : Fin 16)
    (hav : v ≠ a) (hAddr : s.regs 15 + s.regs a < 2 ^ E.W) :
    runBlock (upRelativeStore a v) E s =
      { s with pc := s.pc + 2, regs := Function.update s.regs a (s.regs 15 + s.regs a), mem := Function.update s.mem (s.regs 15 + s.regs a) (s.regs v) } := by
  simp [upRelativeStore, runBlock, execInstr, Function.update, hav,
    Nat.mod_eq_of_lt hAddr, Nat.add_assoc]
theorem upRelativeStore_frame (E : RAMEnv) (s : RAMState) (a v : Fin 16) (words : ℕ)
    (hav : v ≠ a) (hAddr : s.regs 15 + s.regs a < 2 ^ E.W)
    (hWord : s.regs a < words) (q : ℕ)
    (hq : ¬ (s.regs 15 ≤ q ∧ q < s.regs 15 + words)) :
    (runBlock (upRelativeStore a v) E s).mem q = s.mem q := by
  rw [upRelativeStore_spec E s a v hav hAddr]
  apply Function.update_of_ne
  intro he
  apply hq
  rw [he]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hWord _⟩
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
theorem upGuardStore_frame (E : RAMEnv) (p : RAMState) (beta words : ℕ)
    (hBase : p.regs 15 = beta) (hEnd : beta + words ≤ 2 ^ E.W)
    (hSafe : p.regs 3 ≠ 0 → p.regs 2 < words) (q : ℕ)
    (hq : ¬ (beta ≤ q ∧ q < beta + words)) :
    (upGuardStoreResult E p).mem q = p.mem q := by
  by_cases hz : p.regs 3 = 0
  · simp only [upGuardStoreResult, if_pos hz]
  · have hWord := hSafe hz
    have hAddr : p.regs 15 + p.regs 2 < 2 ^ E.W := by rw [hBase]; omega
    rw [upGuardStoreResult, if_neg hz]
    exact upRelativeStore_frame E p 2 11 words (by decide) hAddr hWord q (by simpa [hBase] using hq)
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upBasedBody_frame_of_data (E : RAMEnv) (a betaDet betaPay i words : ℕ)
    (it : UpIt) (ab : UpAbs) (p : RAMState)
    (hData : UpBasedPrefixData E betaDet betaPay i it ab p (upBasedPrefixRun E p))
    (hEnd : betaPay + words ≤ 2 ^ E.W)
    (hSafe : upvMask (upShiftDetEnv E betaDet) i it ab ≠ 0 →
      upvWi (upShiftDetEnv E betaDet) i it ab < words)
    (addr : ℕ) (hAddr : ¬ (betaPay ≤ addr ∧ addr < betaPay + words)) :
    (upBasedBodyResult E a p).mem addr = p.mem addr := by
  rw [upBasedBodyResult_mem]
  have hNativeSafe : (upBasedPrefixRun E p).regs 3 ≠ 0 → (upBasedPrefixRun E p).regs 2 < words := by
    rw [hData.mask, hData.word]
    exact hSafe
  have hh := upGuardStore_frame E (upBasedPrefixRun E p) betaPay words hData.pay hEnd hNativeSafe addr hAddr
  rw [hData.mem] at hh
  exact hh
end LinearSetReconciliation327.Main
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def UpMemFrame (allowed : ℕ → Prop) (p q : RAMState) : Prop :=
  ∀ addr, ¬ allowed addr → q.mem addr = p.mem addr
theorem upSavedPost_save_frame (W beta sav : ℕ) (p q : RAMState)
    (hm : q.mem = Function.update (Function.update p.mem ((beta + sav) % 2 ^ W) (p.regs 8))
      ((beta + (sav + 1)) % 2 ^ W) (p.regs 9)) :
    UpMemFrame (fun addr => addr = (beta + sav) % 2 ^ W ∨ addr = (beta + (sav + 1)) % 2 ^ W) p q := by
  intro addr ha
  rw [hm]
  simp only [not_or] at ha
  simp only [Function.update_apply, if_neg ha.1, if_neg ha.2]
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def UpSavedCells (W beta : ℕ) (it : UpIt) (addr : ℕ) : Prop :=
  2 ≤ it.mode ∧ (addr = (beta + it.sav) % 2 ^ W ∨ addr = (beta + (it.sav + 1)) % 2 ^ W)
theorem upSavedPost_memory (E : RAMEnv) (betaDet betaPay ptr : ℕ) (it : UpIt) (p : RAMState)
    (hKind : UpItemKind it) (h6 : p.regs 6 = 1) (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay)
    (h7 : p.regs 7 = ptr + 16) (h16 : ptr + 16 < 2 ^ E.W)
    (hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = it.mode)
    (hSav : E.det ((betaDet + (ptr + 15)) % 2 ^ E.W) % 2 ^ E.W = it.sav)
    (hc : p.regs 8 < 2 ^ E.W) (hf : p.regs 9 < 2 ^ E.W) :
    (∀ addr, p.mem addr < 2 ^ E.W → (upSavedPostRun E p).mem addr < 2 ^ E.W) ∧
      UpMemFrame (UpSavedCells E.W betaPay it) p (upSavedPostRun E p) := by
  rcases hKind with hLow | ⟨sav, hSave | hRestore⟩
  · have hPost := upSavedPost_normal E p ptr betaDet it.mode h7 h14 h16 hMode hLow
    refine ⟨?_, ?_⟩
    · intro addr ha
      rw [hPost.1]
      exact ha
    · intro addr _
      exact congrFun hPost.1 addr
  · subst it
    have hPost := upSavedPost_save E p ptr betaDet betaPay sav h7 h6 h14 h15 h16 hMode hSav
    refine ⟨?_, ?_⟩
    · intro addr ha
      rw [hPost.1]
      simp only [Function.update_apply]
      split_ifs <;> assumption
    · intro addr ha
      apply upSavedPost_save_frame E.W betaPay sav p _ hPost.1 addr
      intro h
      exact ha ⟨by norm_num [upSave], h⟩
  · subst it
    have hPost := upSavedPost_restore E p ptr betaDet betaPay sav h7 h6 h14 h15 h16 hMode hSav
    refine ⟨?_, ?_⟩
    · intro addr ha
      rw [hPost.1]
      exact ha
    · intro addr _
      exact congrFun hPost.1 addr
theorem upSavedBody_raw_frame_aux (E : RAMEnv) (base betaDet betaPay i ptr words : ℕ)
    (it : UpIt) (ab : UpAbs) (p : RAMState)
    (hView : UpBasedView E.W betaPay ab p) (hRaw : UpBasedRawPayload betaPay words ab p)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + words ≤ 2 ^ E.W)
    (hKind : UpItemKind it) (h6 : p.regs 6 = 1) (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay)
    (h7 : (upBasedBodyResult E base p).regs 7 = ptr + 16) (h16 : ptr + 16 < 2 ^ E.W)
    (hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = it.mode)
    (hSav : E.det ((betaDet + (ptr + 15)) % 2 ^ E.W) % 2 ^ E.W = it.sav)
    (hData : UpBasedPrefixData E betaDet betaPay i it ab p (upBasedPrefixRun E p))
    (hOutView : UpBasedView E.W betaPay (upApply (upShiftDetEnv E betaDet) i it ab)
      (upSavedBodyResult E base p))
    (hSafe : upvMask (upShiftDetEnv E betaDet) i it ab ≠ 0 →
      upvWi (upShiftDetEnv E betaDet) i it ab < words) :
    UpBasedRawPayload betaPay words (upApply (upShiftDetEnv E betaDet) i it ab)
      (upSavedBodyResult E base p) ∧
      UpMemFrame (fun addr => (betaPay ≤ addr ∧ addr < betaPay + words) ∨ UpSavedCells E.W betaPay it addr)
        p (upSavedBodyResult E base p) := by
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
  refine ⟨?_, ?_⟩
  · apply upBasedRaw_initial E.W betaPay words _ _ hOutView hEnd
    intro j hj
    rw [hOut.1]
    apply hPost.1
    rw [hRawB j hj]
    exact upBasedView_bound E.W betaPay _ q hB j
  · intro addr ha
    have hOutside : ¬ (betaPay ≤ addr ∧ addr < betaPay + words) := fun h => ha (Or.inl h)
    have hNotSaved : ¬ UpSavedCells E.W betaPay it addr := fun h => ha (Or.inr h)
    rw [hOut.1, hPost.2 addr hNotSaved]
    exact upBasedBody_frame_of_data E base betaDet betaPay i words it ab p hData hEnd hSafe addr hOutside
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upBasedView_data (W beta : ℕ) (ab : UpAbs) (p q : RAMState)
    (h : UpBasedView W beta ab p) (hm : q.mem = p.mem)
    (hc : q.regs 8 = p.regs 8) (hf : q.regs 9 = p.regs 9) : UpBasedView W beta ab q :=
  ⟨by rw [hm]; exact h.mem, hc.trans h.coord, hf.trans h.flag⟩
theorem upSavedPost_save_view (E : RAMEnv) (beta sav : ℕ) (ab : UpAbs) (p q : RAMState)
    (hView : UpBasedView E.W beta ab p) (hBeta : beta < 2 ^ E.W)
    (hSav : sav + 1 < 2 ^ E.W) (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W)
    (hm : q.mem = Function.update (Function.update p.mem ((beta + sav) % 2 ^ E.W) (p.regs 8))
      ((beta + (sav + 1)) % 2 ^ E.W) (p.regs 9))
    (h8 : q.regs 8 = p.regs 8) (h9 : q.regs 9 = p.regs 9) :
    UpBasedView E.W beta
      ⟨Function.update (Function.update ab.mem sav ab.c) (sav + 1) ab.f, ab.c, ab.f⟩ q := by
  refine ⟨?_, h8.trans hView.coord, h9.trans hView.flag⟩
  rw [hm]
  change upVirtualMem E.W beta
    (Function.update (Function.update p.mem (upCyclicAddr E.W beta sav) (p.regs 8))
      (upCyclicAddr E.W beta (sav + 1)) (p.regs 9)) = _
  rw [upVirtualMem_update E.W beta (sav + 1) _ _ hBeta hSav,
    upVirtualMem_update E.W beta sav _ _ hBeta (by omega), hView.mem,
    hView.coord, hView.flag, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hf]
theorem upSavedPost_restore_view (E : RAMEnv) (beta sav : ℕ) (ab : UpAbs) (p q : RAMState)
    (hView : UpBasedView E.W beta ab p) (hSav : sav + 1 < 2 ^ E.W)
    (hm : q.mem = p.mem)
    (h8 : q.regs 8 = p.mem ((beta + sav) % 2 ^ E.W) % 2 ^ E.W)
    (h9 : q.regs 9 = p.mem ((beta + (sav + 1)) % 2 ^ E.W) % 2 ^ E.W) :
    UpBasedView E.W beta ⟨ab.mem, ab.mem sav, ab.mem (sav + 1)⟩ q := by
  refine ⟨by rw [hm]; exact hView.mem, ?_, ?_⟩
  · have hh := congrFun hView.mem sav
    rw [upVirtualMem, if_pos (by omega : sav < 2 ^ E.W)] at hh
    exact h8.trans hh
  · have hh := congrFun hView.mem (sav + 1)
    rw [upVirtualMem, if_pos hSav] at hh
    exact h9.trans hh
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem function_update_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) :
    Function.update f a (f a) = f := by
  funext x
  rw [Function.update_apply]
  by_cases h : x = a
  · rw [if_pos h, h]
  · rw [if_neg h]
theorem upApply_eq_body (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs)
    (hW : 1 < 2 ^ E.W) (hm : it.mode < 2) (hmem : ∀ x, a.mem x < 2 ^ E.W) :
    upApply E i it a = upApplyBody E i it a := by
  have hM : 0 < 2 ^ E.W := by omega
  have hg2 : upvG2 E it = 1 := by
    unfold upvG2
    rw [if_pos hm, Nat.mod_eq_of_lt hW]
  have hg3 : upvG3 E it = 1 := by
    unfold upvG3
    rw [if_pos (by omega), Nat.mod_eq_of_lt hW]
  have ha2 : upvA2 E it = 0 := by
    unfold upvA2
    rw [hg2, Nat.mod_eq_of_lt hW]
    rw [show 1 + 2 ^ E.W - 1 = 2 ^ E.W by omega, Nat.mod_self]
  have ha3 : upvA3 E it = 0 := by
    unfold upvA3
    rw [hg3, Nat.mod_eq_of_lt hW]
    rw [show 1 + 2 ^ E.W - 1 = 2 ^ E.W by omega, Nat.mod_self]
  have hrt : upvRt E it = 0 := by
    unfold upvRt
    rw [ha3, Nat.mul_zero, Nat.zero_mod]
  have hsv : upvSv E it = 0 := by
    unfold upvSv
    rw [ha2, hrt, Nat.zero_add, Nat.sub_zero, Nat.mod_self]
  have hcnlt : upvCn E i it a < 2 ^ E.W := Nat.mod_lt _ hM
  have hfnlt : upvFn E i it a < 2 ^ E.W := Nat.mod_lt _ hM
  have hcn : upvCnf E i it a = upvCn E i it a := by
    unfold upvCnf
    rw [hrt, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt hcnlt]
  have hfn : upvFnf E i it a = upvFn E i it a := by
    unfold upvFnf
    rw [hrt, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt hfnlt]
  have hbm : ∀ x, (upApplyBody E i it a).mem x < 2 ^ E.W := by
    intro x
    show (Function.update a.mem (upvWi E i it a) (upvNew E i it a)) x < 2 ^ E.W
    rw [Function.update_apply]
    by_cases hx : x = upvWi E i it a
    · rw [if_pos hx]; exact Nat.mod_lt _ hM
    · rw [if_neg hx]; exact hmem x
  have hm0 : upvM0 E i it a = (upApplyBody E i it a).mem it.sav := Nat.mod_eq_of_lt (hbm _)
  have hm1 : upvM1 E i it a = (upApplyBody E i it a).mem (it.sav + 1) := Nat.mod_eq_of_lt (hbm _)
  have hm0lt : upvM0 E i it a < 2 ^ E.W := Nat.mod_lt _ hM
  have hm1lt : upvM1 E i it a < 2 ^ E.W := Nat.mod_lt _ hM
  have hv0 : upvV0 E i it a = upvM0 E i it a := by
    unfold upvV0
    rw [hsv, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hm0lt]
  have hv1 : upvV1 E i it a = upvM1 E i it a := by
    unfold upvV1
    rw [hsv, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hm1lt]
  show upApply E i it a = upApplyBody E i it a
  unfold upApply
  rw [hcn, hfn, hv0, hv1, hm0, hm1, function_update_self, function_update_self]
  rfl
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
theorem upvCn_of_setSt0 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hst : it.setSt = 0) (hc : ab.c < 2 ^ E.W) :
    upvCn E i it ab = ab.c := by
  unfold upvCn upvY2
  rw [hst, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt hc]
theorem upvFn_of_setSt0 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hst : it.setSt = 0) (hf : ab.f < 2 ^ E.W) :
    upvFn E i it ab = ab.f := by
  unfold upvFn upvY11
  rw [hst, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt hf]
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem up_mod_blend_left (M a b : ℕ) (ha : a < M) (hb : b < M) :
    (a + (b + M - a) % M) % M = b := by
  calc
    _ = (a + (b + M - a)) % M := by simp only [Nat.add_mod, Nat.mod_mod]
    _ = (b + M) % M := by congr 1; omega
    _ = b := by simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hb]
theorem up_mod_blend_right (M a b : ℕ) (ha : a < M) (hb : b < M) :
    ((a + M - b) % M + b) % M = a := by
  calc
    _ = ((a + M - b) + b) % M := by simp only [Nat.add_mod, Nat.mod_mod]
    _ = (a + M) % M := by congr 1; omega
    _ = a := by simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt ha]
theorem upApplyBody_idle_mem (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs)
    (hm : it.mOn = 0) (hmem : ∀ x, a.mem x < 2 ^ E.W) :
    (upApplyBody E i it a).mem = a.mem := by
  have hmask : upvMask E i it a = 0 := by simp only [upvMask, upvMask0, hm, Nat.mul_zero, Nat.zero_mod, Nat.zero_mul]
  have hnew : upvNew E i it a = a.mem (upvWi E i it a) := by
    simp only [upvNew, hmask, Nat.xor_zero, upvOld, Nat.mod_mod, Nat.mod_eq_of_lt (hmem _)]
  change Function.update a.mem (upvWi E i it a) (upvNew E i it a) = a.mem
  rw [hnew, function_update_self]
theorem upSave_apply (E : RAMEnv) (i sav : ℕ) (a : UpAbs)
    (hW : 1 < 2 ^ E.W) (hc : a.c < 2 ^ E.W) (hf : a.f < 2 ^ E.W)
    (hmem : ∀ x, a.mem x < 2 ^ E.W) :
    upApply E i (upSave sav) a =
      ⟨Function.update (Function.update a.mem sav a.c) (sav + 1) a.f, a.c, a.f⟩ := by
  have hm := upApplyBody_idle_mem E i (upSave sav) a rfl hmem
  have hcn : upvCn E i (upSave sav) a = a.c := by
    simp only [upvCn, upvY2, upSave, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt hc]
  have hfn : upvFn E i (upSave sav) a = a.f := by
    simp only [upvFn, upvY11, upSave, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt hf]
  have hrt : upvRt E (upSave sav) = 0 := by simp only [upvRt, upSave, Nat.zero_mul, Nat.zero_mod]
  have hsv : upvSv E (upSave sav) = 1 := by
    unfold upvSv
    rw [hrt]
    simp [upvA2, upvG2, upSave, Nat.mod_eq_of_lt hW, Nat.add_mod]
  have hm0 : upvM0 E i (upSave sav) a = a.mem sav := by
    unfold upvM0
    rw [hm]
    exact Nat.mod_eq_of_lt (hmem _)
  have hm1 : upvM1 E i (upSave sav) a = a.mem (sav + 1) := by
    unfold upvM1
    rw [hm]
    exact Nat.mod_eq_of_lt (hmem _)
  have hcnf : upvCnf E i (upSave sav) a = a.c := by
    simp only [upvCnf, hrt, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, hcn, Nat.mod_eq_of_lt hc]
  have hfnf : upvFnf E i (upSave sav) a = a.f := by
    simp only [upvFnf, hrt, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, hfn, Nat.mod_eq_of_lt hf]
  have hv0 : upvV0 E i (upSave sav) a = a.c := by
    rw [upvV0, hcnf, hm0, hsv, Nat.mul_one, Nat.mod_mod]
    exact up_mod_blend_right _ _ _ hc (hmem _)
  have hv1 : upvV1 E i (upSave sav) a = a.f := by
    rw [upvV1, hfnf, hm1, hsv, Nat.mul_one, Nat.mod_mod]
    exact up_mod_blend_right _ _ _ hf (hmem _)
  unfold upApply
  rw [hm, hcnf, hfnf, hv0, hv1]
  rfl
theorem upRestore_apply (E : RAMEnv) (i sav : ℕ) (a : UpAbs)
    (hW : 1 < 2 ^ E.W) (hmem : ∀ x, a.mem x < 2 ^ E.W) :
    upApply E i (upRestore sav) a = ⟨a.mem, a.mem sav, a.mem (sav + 1)⟩ := by
  have hm := upApplyBody_idle_mem E i (upRestore sav) a rfl hmem
  have hrt : upvRt E (upRestore sav) = 1 := by
    simp [upvRt, upvA3, upvG3, upRestore, Nat.mod_eq_of_lt hW, Nat.add_mod]
  have hsv : upvSv E (upRestore sav) = 0 := by
    unfold upvSv
    rw [hrt]
    simp [upvA2, upvG2, upRestore, Nat.mod_eq_of_lt hW, Nat.add_mod]
  have hm0 : upvM0 E i (upRestore sav) a = a.mem sav := by
    unfold upvM0
    rw [hm]
    exact Nat.mod_eq_of_lt (hmem _)
  have hm1 : upvM1 E i (upRestore sav) a = a.mem (sav + 1) := by
    unfold upvM1
    rw [hm]
    exact Nat.mod_eq_of_lt (hmem _)
  have hcnf : upvCnf E i (upRestore sav) a = a.mem sav := by
    rw [upvCnf, hrt, Nat.mul_one, Nat.mod_mod, hm0]
    exact up_mod_blend_left _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos E.W)) (hmem _)
  have hfnf : upvFnf E i (upRestore sav) a = a.mem (sav + 1) := by
    rw [upvFnf, hrt, Nat.mul_one, Nat.mod_mod, hm1]
    exact up_mod_blend_left _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos E.W)) (hmem _)
  have hv0 : upvV0 E i (upRestore sav) a = a.mem sav := by
    simp only [upvV0, hsv, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, hm0, Nat.mod_eq_of_lt (hmem _)]
  have hv1 : upvV1 E i (upRestore sav) a = a.mem (sav + 1) := by
    simp only [upvV1, hsv, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, hm1, Nat.mod_eq_of_lt (hmem _)]
  unfold upApply
  rw [hm, hcnf, hfnf, hv0, hv1]
  simp only [upRestore]
  rw [function_update_self, function_update_self]
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upAbs_ext (a b : UpAbs) (hm : a.mem = b.mem) (hc : a.c = b.c) (hf : a.f = b.f) : a = b := by
  cases a
  cases b
  simp_all
theorem upApplyBody_save_eq (E : RAMEnv) (i sav : ℕ) (ab : UpAbs)
    (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W) (hm : ∀ j, ab.mem j < 2 ^ E.W) :
    upApplyBody E i (upSave sav) ab = ab := by
  apply upAbs_ext
  · exact upApplyBody_idle_mem E i (upSave sav) ab rfl hm
  · exact upvCn_of_setSt0 E i (upSave sav) ab rfl hc
  · exact upvFn_of_setSt0 E i (upSave sav) ab rfl hf
theorem upSavedBody_view_of_data (E : RAMEnv) (base betaDet betaPay i ptr : ℕ)
    (it : UpIt) (ab : UpAbs) (p : RAMState)
    (hView : UpBasedView E.W betaPay ab p) (hPay : betaPay < 2 ^ E.W)
    (hW : 1 < 2 ^ E.W) (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W)
    (hKind : UpItemKind it) (hSlots : 2 ≤ it.mode → it.sav + 1 < 2 ^ E.W)
    (h6 : p.regs 6 = 1) (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay)
    (h7 : (upBasedBodyResult E base p).regs 7 = ptr + 16) (h16 : ptr + 16 < 2 ^ E.W)
    (hMode : E.det ((betaDet + (ptr + 10)) % 2 ^ E.W) % 2 ^ E.W = it.mode)
    (hSav : E.det ((betaDet + (ptr + 15)) % 2 ^ E.W) % 2 ^ E.W = it.sav)
    (hData : UpBasedPrefixData E betaDet betaPay i it ab p (upBasedPrefixRun E p)) :
    UpBasedView E.W betaPay (upApply (upShiftDetEnv E betaDet) i it ab)
      (upSavedBodyResult E base p) := by
  let F := upShiftDetEnv E betaDet
  let q := upBasedBodyResult E base p
  have hMem := upBasedView_bound E.W betaPay ab p hView
  have hQ := upBasedBodyResult_meta E base p
  have hQ6 : q.regs 6 = 1 := (hQ.2.2.2 6 (by tauto)).trans h6
  have hQ14 : q.regs 14 = betaDet := (hQ.2.2.2 14 (by tauto)).trans h14
  have hQ15 : q.regs 15 = betaPay := (hQ.2.2.2 15 (by tauto)).trans h15
  have hB := upBasedBody_view_of_data E base betaDet betaPay i it ab p hView hPay hData
  have hPost : UpBasedView E.W betaPay (upApply F i it ab) (upSavedPostRun E q) := by
    rcases hKind with hLow | ⟨sav, hSave | hRestore⟩
    · have hNormal := upSavedPost_normal E q ptr betaDet it.mode h7 hQ14 h16 hMode hLow
      rw [upApply_eq_body F i it ab hW hLow hMem]
      exact upBasedView_data E.W betaPay _ q _ hB hNormal.1 hNormal.2.1 hNormal.2.2
    · subst it
      have hB' : UpBasedView E.W betaPay ab q := by
        change UpBasedView E.W betaPay (upApplyBody F i (upSave sav) ab) q at hB
        rw [upApplyBody_save_eq F i sav ab hc hf hMem] at hB
        exact hB
      have hSave := upSavedPost_save E q ptr betaDet betaPay sav h7 hQ6 hQ14 hQ15 h16 hMode hSav
      rw [upSave_apply F i sav ab hW hc hf hMem]
      exact upSavedPost_save_view E betaPay sav ab q _ hB' hPay (hSlots (by norm_num [upSave])) hc hf
        hSave.1 hSave.2.1 hSave.2.2
    · subst it
      have hRestore := upSavedPost_restore E q ptr betaDet betaPay sav h7 hQ6 hQ14 hQ15 h16 hMode hSav
      have hV := upSavedPost_restore_view E betaPay sav (upApplyBody F i (upRestore sav) ab)
        q _ hB (hSlots (by norm_num [upRestore])) hRestore.1 hRestore.2.1 hRestore.2.2
      have hIdle := upApplyBody_idle_mem F i (upRestore sav) ab rfl hMem
      rw [hIdle] at hV
      rw [upRestore_apply F i sav ab hW hMem]
      exact hV
  have hOut := upSavedBodyResult_data E base p
  exact upBasedView_data E.W betaPay _ _ _ hPost hOut.1 hOut.2.1 hOut.2.2
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upBasedNext_pointer (E : RAMEnv) (p : RAMState) (j : ℕ)
    (h5 : p.regs 5 = j) (h16 : 16 < 2 ^ E.W) (h8 : 8 < 2 ^ E.W)
    (hAddr : 8 + 16 * j < 2 ^ E.W) :
    (runBlock upBasedNext E p).regs 7 = 8 + 16 * j := by
  have hMul : 16 * j < 2 ^ E.W := by omega
  have hAdd : 16 * j + 8 < 2 ^ E.W := by omega
  simp [upBasedNext, runBlock, execInstr, Function.update_apply, h5,
    Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt hMul,
    Nat.mod_eq_of_lt hAdd, Nat.mod_eq_of_lt hAddr, Nat.add_comm]
theorem upBasedBodyResult_pointer (E : RAMEnv) (a : ℕ) (p : RAMState)
    (h16 : 16 < 2 ^ E.W) (h8 : 8 < 2 ^ E.W)
    (hAddr : 8 + 16 * ((p.regs 5 + p.regs 6) % 2 ^ E.W) < 2 ^ E.W) :
    (upBasedBodyResult E a p).regs 7 = 8 + 16 * ((p.regs 5 + p.regs 6) % 2 ^ E.W) := by
  let q := upBasedPrefixRun E p
  let u : RAMState := { upGuardStoreResult E q with pc := a + 112 }
  have hU5 : u.regs 5 = (p.regs 5 + p.regs 6) % 2 ^ E.W :=
    (upGuardStore_register_frame E q 5 (by decide)).trans (upBasedPrefix_meta E p).1
  have hEq : upBasedBodyResult E a p = runBlock (upBasedNext ++ upBasedCount) E u := by
    rw [upBasedBodyResult_eq, ← upBasedPrefixRun_eq]
  rw [hEq, runBlock_append, upBlock_register_frame upBasedCount E _ 7 (by simp [upBasedCount, upRegTarget])]
  exact upBasedNext_pointer E u _ hU5 h16 h8 hAddr
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem upSavedBody_effect (E : RAMEnv) (p : RAMState) (base betaDet betaPay i j words : ℕ)
    (it : UpIt) (ab : UpAbs)
    (hView : UpBasedView E.W betaPay ab p) (hRaw : UpBasedRawPayload betaPay words ab p)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + words ≤ 2 ^ E.W)
    (hW : 1 < 2 ^ E.W) (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W)
    (hKind : UpItemKind it) (hSlots : 2 ≤ it.mode → it.sav + 1 < 2 ^ E.W)
    (h0 : p.regs 0 = i) (h5 : p.regs 5 = j) (h6 : p.regs 6 = 1)
    (h7 : p.regs 7 = 8 + 16 * j) (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay)
    (hAddr : 8 + 16 * (j + 1) < 2 ^ E.W)
    (hFields : ∀ t, t < 16 → (upShiftDetEnv E betaDet).det (8 + 16 * j + t) % 2 ^ E.W = it.fld t)
    (hWidth : upvWw (upShiftDetEnv E betaDet) = E.W)
    (hSafe : upvMask (upShiftDetEnv E betaDet) i it ab ≠ 0 →
      upvWi (upShiftDetEnv E betaDet) i it ab < words) :
    UpBasedView E.W betaPay (upApply (upShiftDetEnv E betaDet) i it ab) (upSavedBodyResult E base p) ∧
      UpBasedRawPayload betaPay words (upApply (upShiftDetEnv E betaDet) i it ab) (upSavedBodyResult E base p) ∧
      UpMemFrame (fun addr => (betaPay ≤ addr ∧ addr < betaPay + words) ∨ UpSavedCells E.W betaPay it addr)
        p (upSavedBodyResult E base p) := by
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
  have hR := upSavedBody_raw_frame_aux E base betaDet betaPay i ptr words it ab p hView hRaw hPay hEnd
    hKind h6 h14 h15 hNext h16 hMode hSav hData hV hSafe
  exact ⟨hV, hR⟩

end LinearSetReconciliation327.Main



#print axioms LinearSetReconciliation327.Main.upSavedBody_effect


