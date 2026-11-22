-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpdateLoop20261120
-- name    : LinearSetReconciliation327_Main_HintUpdateLoop20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:42:49.12482+00:00
-- url     : https://prove2.me/theorems/8c0f0e80-6f14-4ac1-a7b8-233496726705
-- title:
--   LinearSetReconciliation327 — HintUpdateLoop (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpdateLoop20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateMemory20261120
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
def upFiniteNoWrite (r : Fin 16) : Stmt → Prop
  | .code code => ∀ op ∈ code, upRegTarget op ≠ some r
  | .seq left right => upFiniteNoWrite r left ∧ upFiniteNoWrite r right
  | .ite c left right =>
      (∀ op ∈ c.code, upRegTarget op ≠ some r) ∧ upFiniteNoWrite r left ∧ upFiniteNoWrite r right
  | .loop _ _ => False
theorem upFiniteEval_register_frame (E : RAMEnv) (stmt : Stmt) (r : Fin 16)
    (hNo : upFiniteNoWrite r stmt) (p : RAMState) :
    (upFiniteEval E stmt p).regs r = p.regs r := by
  revert hNo
  induction stmt generalizing p with
  | code code => intro hNo; exact upBlock_register_frame code E p r hNo
  | seq left right ihLeft ihRight =>
      intro hNo
      exact (ihRight _ hNo.2).trans (ihLeft p hNo.1)
  | ite c left right ihLeft ihRight =>
      intro hNo
      have hC := upBlock_register_frame c.code E p r hNo.1
      simp only [upFiniteEval]
      split
      · exact (ihRight _ hNo.2.2).trans hC
      · exact (ihLeft _ hNo.2.1).trans hC
  | loop c body ih => intro hNo; exact False.elim hNo
theorem upSavedPostRun_eq (E : RAMEnv) (p : RAMState) :
    upSavedPostRun E p = upFiniteEval E upSavedPost p := by unfold upSavedPostRun <;> rfl
theorem upSavedPost_no_write (r : Fin 16)
    (hr : r = 0 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 14 ∨ r = 15) : upFiniteNoWrite r upSavedPost := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [upFiniteNoWrite, upSavedPost, upSavedMode, upSavedSlot, upSavedWrite,
      upSavedRead, Cond.code, upRegTarget]
theorem upSavedPostRun_frame (E : RAMEnv) (p : RAMState) (r : Fin 16)
    (hr : r = 0 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 14 ∨ r = 15) :
    (upSavedPostRun E p).regs r = p.regs r := by
  rw [upSavedPostRun_eq]
  exact upFiniteEval_register_frame E upSavedPost r (upSavedPost_no_write r hr) p
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upBasedCount_length : upBasedCount.length = 3 := rfl
theorem upBasedCount_noBranch : NoBranch upBasedCount := by
  simp [upBasedCount, NoBranch, Instr.NoBranchI]
theorem upSavedBodyResult_meta (E : RAMEnv) (base : ℕ) (p : RAMState) :
    (upSavedBodyResult E base p).pc = base + 145 ∧
      (upSavedBodyResult E base p).regs 5 = (p.regs 5 + p.regs 6) % 2 ^ E.W ∧
      (upSavedBodyResult E base p).regs 1 = E.det (p.regs 14 % 2 ^ E.W) % 2 ^ E.W ∧
      (∀ r, r = 0 ∨ r = 6 ∨ r = 14 ∨ r = 15 →
        (upSavedBodyResult E base p).regs r = p.regs r) := by
  let q := upBasedBodyResult E base p
  let u : RAMState := { upSavedPostRun E q with pc := base + 142 }
  have hQ := upBasedBodyResult_meta E base p
  have hEq : upSavedBodyResult E base p = runBlock upBasedCount E u := upSavedBodyResult_eq E base p
  have hFr : ∀ r, r ≠ 1 → (r = 0 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 14 ∨ r = 15) →
      (runBlock upBasedCount E u).regs r = q.regs r := by
    intro r h1 hr
    exact (upBlock_register_frame upBasedCount E u r (by simp [upBasedCount, upRegTarget, Ne.symm h1])).trans
      (upSavedPostRun_frame E q r hr)
  have hBase : u.regs 14 = p.regs 14 :=
    (upSavedPostRun_frame E q 14 (by tauto)).trans (hQ.2.2.2 14 (by tauto))
  simp only [hEq]
  refine ⟨?_, (hFr 5 (by decide) (by tauto)).trans hQ.2.1, ?_, ?_⟩
  · rw [runBlock_pc upBasedCount E u upBasedCount_noBranch, upBasedCount_length]
  · rw [upBasedCount_spec, hBase]
  · intro r hr
    have h1 : r ≠ 1 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    have hAll : r = 0 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 14 ∨ r = 15 := by tauto
    exact (hFr r h1 hAll).trans (hQ.2.2.2 r hr)
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
namespace LinearSetReconciliation327.Main
theorem upBasedTest_frame (E : RAMEnv) (s : RAMState) (r : Fin 16) (hr : r ≠ 4) :
    (runBlock upBasedTest.code E s).regs r = s.regs r := by
  simp [upBasedTest, Cond.code, runBlock, execInstr, Function.update_apply, hr]
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upSavedLoopStep (E : RAMEnv) (head : ℕ) (s : RAMState) : RAMState :=
  let entry : RAMState := { runBlock upBasedTest.code E s with pc := head + 2 }
  { upSavedBodyResult E (head + 2) entry with pc := head }
theorem upSavedLoopStep_eq (E : RAMEnv) (head : ℕ) (s : RAMState) :
    upSavedLoopStep E head s =
      { upSavedBodyResult E (head + 2)
        { runBlock upBasedTest.code E s with pc := head + 2 } with pc := head } := by unfold upSavedLoopStep <;> rfl
attribute [irreducible] upSavedLoopStep
theorem upSavedLoopStep_meta (E : RAMEnv) (head : ℕ) (s : RAMState) :
    (upSavedLoopStep E head s).pc = head ∧
      (upSavedLoopStep E head s).regs 5 = (s.regs 5 + s.regs 6) % 2 ^ E.W ∧
      (upSavedLoopStep E head s).regs 1 = E.det (s.regs 14 % 2 ^ E.W) % 2 ^ E.W ∧
      (∀ r, r = 0 ∨ r = 6 ∨ r = 14 ∨ r = 15 →
        (upSavedLoopStep E head s).regs r = s.regs r) := by
  let entry : RAMState := { runBlock upBasedTest.code E s with pc := head + 2 }
  have hBody := upSavedBodyResult_meta E (head + 2) entry
  rw [upSavedLoopStep_eq]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact hBody.2.1.trans (by
      rw [show entry.regs 5 = s.regs 5 from upBasedTest_frame E s 5 (by decide),
        show entry.regs 6 = s.regs 6 from upBasedTest_frame E s 6 (by decide)])
  · exact hBody.2.2.1.trans (by
      rw [show entry.regs 14 = s.regs 14 from upBasedTest_frame E s 14 (by decide)])
  · intro r hr
    have h4 : r ≠ 4 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
    exact (hBody.2.2.2 r hr).trans (upBasedTest_frame E s r h4)
def upSavedLoopState (E : RAMEnv) (head : ℕ) (seed : RAMState) : ℕ → RAMState
  | 0 => seed
  | j + 1 => upSavedLoopStep E head (upSavedLoopState E head seed j)
@[simp] theorem upSavedLoopState_zero (E : RAMEnv) (head : ℕ) (seed : RAMState) :
    upSavedLoopState E head seed 0 = seed := rfl
theorem upSavedLoopState_succ (E : RAMEnv) (head : ℕ) (seed : RAMState) (j : ℕ) :
    upSavedLoopState E head seed (j + 1) = upSavedLoopStep E head (upSavedLoopState E head seed j) := rfl
structure UpSavedReady (beta L j : ℕ) (s : RAMState) : Prop where
  counter : s.regs 5 = j
  one : s.regs 6 = 1
  count : s.regs 1 = L
  base : s.regs 14 = beta
theorem upSavedLoopState_ready (E : RAMEnv) (head beta L : ℕ) (seed : RAMState)
    (hSeed : UpSavedReady beta L 0 seed) (hL : L < 2 ^ E.W)
    (hCount : E.det (beta % 2 ^ E.W) % 2 ^ E.W = L) :
    ∀ j, j ≤ L → UpSavedReady beta L j (upSavedLoopState E head seed j) := by
  intro j
  induction j with
  | zero => intro _; exact hSeed
  | succ j ih =>
      intro hj
      have hPrev := ih (by omega)
      have hNext := upSavedLoopStep_meta E head (upSavedLoopState E head seed j)
      rw [upSavedLoopState_succ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hNext.2.1, hPrev.counter, hPrev.one, Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ E.W)]
      · exact (hNext.2.2.2 6 (Or.inr (Or.inl rfl))).trans hPrev.one
      · rw [hNext.2.2.1, hPrev.base, hCount]
      · exact (hNext.2.2.2 14 (Or.inr (Or.inr (Or.inl rfl)))).trans hPrev.base
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
namespace LinearSetReconciliation327.Main
theorem upSavedBodyResult_pointer (E : RAMEnv) (base : ℕ) (p : RAMState)
    (h16 : 16 < 2 ^ E.W) (h8 : 8 < 2 ^ E.W)
    (hAddr : 8 + 16 * ((p.regs 5 + p.regs 6) % 2 ^ E.W) < 2 ^ E.W) :
    (upSavedBodyResult E base p).regs 7 = 8 + 16 * ((p.regs 5 + p.regs 6) % 2 ^ E.W) := by
  rw [upSavedBodyResult_eq,
    upBlock_register_frame upBasedCount E _ 7 (by simp [upBasedCount, upRegTarget])]
  exact (upSavedPostRun_frame E _ 7 (by tauto)).trans (upBasedBodyResult_pointer E base p h16 h8 hAddr)
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def upFold (E : RAMEnv) (i : ℕ) : UpAbs → List UpIt → UpAbs
  | a, [] => a
  | a, it :: rest => upFold E i (upApply E i it a) rest
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upFold_take_succ (E : RAMEnv) (i : ℕ) :
    ∀ (items : List UpIt) (ab : UpAbs) (j : ℕ) (hj : j < items.length),
      upFold E i ab (items.take (j + 1)) = upApply E i items[j] (upFold E i ab (items.take j)) := by
  intro items
  induction items with
  | nil => intro ab j hj; simp at hj
  | cons it rest ih =>
      intro ab j hj
      cases j with
      | zero => rfl
      | succ j =>
          have hjrest : j < rest.length := by simpa using hj
          change upFold E i (upApply E i it ab) (rest.take (j + 1)) =
            upApply E i rest[j] (upFold E i (upApply E i it ab) (rest.take j))
          exact ih (upApply E i it ab) j hjrest
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upBasedTest_mem (E : RAMEnv) (p : RAMState) :
    (runBlock upBasedTest.code E p).mem = p.mem := rfl
theorem upApply_cf_bound (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    (upApply E i it ab).c < 2 ^ E.W ∧ (upApply E i it ab).f < 2 ^ E.W :=
  ⟨Nat.mod_lt _ (Nat.two_pow_pos E.W), Nat.mod_lt _ (Nat.two_pow_pos E.W)⟩
theorem upFold_cf_bound (E : RAMEnv) (i : ℕ) (items : List UpIt) (ab : UpAbs)
    (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W) :
    (upFold E i ab items).c < 2 ^ E.W ∧ (upFold E i ab items).f < 2 ^ E.W := by
  induction items generalizing ab with
  | nil => exact ⟨hc, hf⟩
  | cons it rest ih =>
      have hh := upApply_cf_bound E i it ab
      exact ih _ hh.1 hh.2
theorem upSavedLoopState_pointer (E : RAMEnv) (head beta L : ℕ) (seed : RAMState)
    (hSeed : UpSavedReady beta L 0 seed) (hSeedPtr : seed.regs 7 = 8)
    (hL : L < 2 ^ E.W) (hCount : E.det (beta % 2 ^ E.W) % 2 ^ E.W = L)
    (h16 : 16 < 2 ^ E.W) (hAddr : 8 + 16 * L < 2 ^ E.W) :
    ∀ j, j ≤ L → (upSavedLoopState E head seed j).regs 7 = 8 + 16 * j := by
  intro j hj
  cases j with
  | zero => simpa only [upSavedLoopState_zero, Nat.mul_zero, Nat.add_zero] using hSeedPtr
  | succ j =>
      let p := upSavedLoopState E head seed j
      let entry : RAMState := { runBlock upBasedTest.code E p with pc := head + 2 }
      have hR := upSavedLoopState_ready E head beta L seed hSeed hL hCount j (by omega)
      have h5 : entry.regs 5 = j := (upBasedTest_frame E p 5 (by decide)).trans hR.counter
      have h6 : entry.regs 6 = 1 := (upBasedTest_frame E p 6 (by decide)).trans hR.one
      have hCtr : (entry.regs 5 + entry.regs 6) % 2 ^ E.W = j + 1 := by
        rw [h5, h6, Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ E.W)]
      have hOut := upSavedBodyResult_pointer E (head + 2) entry h16 (by omega)
        (by rw [hCtr]; omega)
      rw [hCtr] at hOut
      rw [upSavedLoopState_succ, upSavedLoopStep_eq]
      exact hOut
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
theorem upSavedLoopState_frame (E : RAMEnv) (head : ℕ) (seed : RAMState)
    (r : Fin 16) (hr : r = 0 ∨ r = 14 ∨ r = 15) :
    ∀ j, (upSavedLoopState E head seed j).regs r = seed.regs r := by
  intro j
  induction j with
  | zero => rfl
  | succ j =>
      rw [upSavedLoopState_succ]
      have hR : r = 0 ∨ r = 6 ∨ r = 14 ∨ r = 15 := by tauto
      exact ((upSavedLoopStep_meta E head _).2.2.2 r hR).trans (by assumption)
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def UpSavedItemSemantics (E : RAMEnv) : Prop :=
  ∀ (p : RAMState) (base betaDet betaPay i j words : ℕ)
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
      upvWi (upShiftDetEnv E betaDet) i it ab < words),
    UpBasedView E.W betaPay (upApply (upShiftDetEnv E betaDet) i it ab) (upSavedBodyResult E base p) ∧
      UpBasedRawPayload betaPay words (upApply (upShiftDetEnv E betaDet) i it ab) (upSavedBodyResult E base p) ∧
      UpMemFrame (fun addr => (betaPay ≤ addr ∧ addr < betaPay + words) ∨ UpSavedCells E.W betaPay it addr)
        p (upSavedBodyResult E base p)
structure UpSavedLayout (E : RAMEnv) (betaDet : ℕ) (items : List UpIt) : Prop where
  end_addr : 8 + 16 * items.length < 2 ^ E.W
  fields : ∀ (j : ℕ) (hj : j < items.length) (t : ℕ), t < 16 →
    (upShiftDetEnv E betaDet).det (8 + 16 * j + t) % 2 ^ E.W = (items[j]'hj).fld t
  width : upvWw (upShiftDetEnv E betaDet) = E.W
  kind : ∀ it ∈ items, UpItemKind it
  slots : ∀ it ∈ items, 2 ≤ it.mode → it.sav + 1 < 2 ^ E.W
def UpSavedAllCells (W beta : ℕ) (items : List UpIt) (addr : ℕ) : Prop :=
  ∃ it ∈ items, UpSavedCells W beta it addr
def UpSavedAllowed (W beta words : ℕ) (items : List UpIt) (addr : ℕ) : Prop :=
  (beta ≤ addr ∧ addr < beta + words) ∨ UpSavedAllCells W beta items addr
theorem upSavedLoopState_effect (E : RAMEnv) (hNative : UpSavedItemSemantics E)
    (head betaDet betaPay i words : ℕ) (items : List UpIt) (seed : RAMState) (ab : UpAbs)
    (hLayout : UpSavedLayout E betaDet items)
    (hView : UpBasedView E.W betaPay ab seed) (hRaw : UpBasedRawPayload betaPay words ab seed)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + words ≤ 2 ^ E.W)
    (h16 : 16 < 2 ^ E.W) (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W)
    (hReady : UpSavedReady betaDet items.length 0 seed) (hPtr : seed.regs 7 = 8)
    (h0 : seed.regs 0 = i) (h15 : seed.regs 15 = betaPay)
    (hCount : E.det (betaDet % 2 ^ E.W) % 2 ^ E.W = items.length)
    (hSafe : ∀ (j : ℕ) (hj : j < items.length),
      let a := upFold (upShiftDetEnv E betaDet) i ab (items.take j)
      upvMask (upShiftDetEnv E betaDet) i (items[j]'hj) a ≠ 0 →
        upvWi (upShiftDetEnv E betaDet) i (items[j]'hj) a < words) :
    ∀ j, j ≤ items.length →
      UpBasedView E.W betaPay (upFold (upShiftDetEnv E betaDet) i ab (items.take j))
        (upSavedLoopState E head seed j) ∧
      UpBasedRawPayload betaPay words (upFold (upShiftDetEnv E betaDet) i ab (items.take j))
        (upSavedLoopState E head seed j) ∧
      UpMemFrame (UpSavedAllowed E.W betaPay words items) seed (upSavedLoopState E head seed j) := by
  have hW : 1 < 2 ^ E.W := by omega
  have hL : items.length < 2 ^ E.W := by have hh := hLayout.end_addr; omega
  have hReadyAll := upSavedLoopState_ready E head betaDet items.length seed hReady hL hCount
  have hPtrAll := upSavedLoopState_pointer E head betaDet items.length seed hReady hPtr hL hCount h16 hLayout.end_addr
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨?_, ?_, ?_⟩
      · simpa only [List.take_zero, upFold, upSavedLoopState_zero] using hView
      · simpa only [List.take_zero, upFold, upSavedLoopState_zero] using hRaw
      · intro addr _; rfl
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
        exact hPrev.2.1 q hq
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
      have hEff := hNative entry (head + 2) betaDet betaPay i j words it a hEntryView hEntryRaw hPay hEnd
        hW hCF.1 hCF.2 (hLayout.kind it hMember) (hLayout.slots it hMember)
        hE0 hE5 hE6 hE7 hE14 hE15 (by have hh := hLayout.end_addr; omega)
        (hLayout.fields j hjL) hLayout.width (hSafe j hjL)
      have hFold := upFold_take_succ (upShiftDetEnv E betaDet) i items ab j hjL
      refine ⟨?_, ?_, ?_⟩
      · rw [hFold, upSavedLoopState_succ, upSavedLoopStep_eq]
        exact ⟨hEff.1.mem, hEff.1.coord, hEff.1.flag⟩
      · rw [hFold, upSavedLoopState_succ, upSavedLoopStep_eq]
        exact hEff.2.1
      · intro addr hOutside
        have hOutsideStep : ¬ ((betaPay ≤ addr ∧ addr < betaPay + words) ∨ UpSavedCells E.W betaPay it addr) := by
          intro h
          rcases h with hPayload | hSlot
          · exact hOutside (Or.inl hPayload)
          · exact hOutside (Or.inr ⟨it, hMember, hSlot⟩)
        have hStep := hEff.2.2 addr hOutsideStep
        rw [upSavedLoopState_succ, upSavedLoopStep_eq]
        exact hStep.trans ((congrFun hMemEntry addr).trans (hPrev.2.2 addr hOutside))
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
def upGuardStore : Stmt := .ite (.neqz 3) (.code (upRelativeStore 2 11)) (.code [])
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upBasedBody : Stmt :=
  .seq (.code upBasedPrefixCode) (.seq upGuardStore (.code (upBasedNext ++ upBasedCount)))
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
namespace LinearSetReconciliation327.Main
def upSavedBody : Stmt := .seq upBasedBody (.seq upSavedPost (.code upBasedCount))
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
theorem upBasedPrefixCode_length : upBasedPrefixCode.length = 107 := rfl
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upGuardStore_sem (P : Program) (E : RAMEnv) (a : ℕ) (s : RAMState)
    (hAt : At P a (upGuardStore.compile a)) (hOne : 1 < 2 ^ E.W) (hpc : s.pc = a) :
    Sem P E a (a + upGuardStore.len) s
      (fun k out => k ≤ 4 ∧ out = { upGuardStoreResult E s with pc := a + upGuardStore.len }) := by
  have hBranches := at_ite (show At P a ((Stmt.ite (.neqz 3)
    (.code (upRelativeStore 2 11)) (.code [])).compile a) from hAt)
  have hTrue := hBranches.2.2.1
  have hFalse := hBranches.2.2.2.2.1
  have hT : NoBranch (upRelativeStore 2 11) := by
    simp [upRelativeStore, NoBranch, Instr.NoBranchI]
  have hSem := Sem.ite P E a (.neqz 3) (.code (upRelativeStore 2 11)) (.code []) s
    (fun k out => k ≤ 4 ∧ out = { upGuardStoreResult E s with pc := a + upGuardStore.len })
    hAt hOne hpc
  apply hSem
  · intro hgo
    have hgo' : s.regs 3 ≠ 0 := hgo
    have hB := Sem.block P E (a + 0 + 1) (upRelativeStore 2 11)
      { s with pc := a + 0 + 1 } hTrue hT rfl
    apply Sem.mono hB
    intro k out hk
    obtain ⟨rfl, rfl⟩ := hk
    constructor
    · norm_num [Cond.code, upRelativeStore]
    · simp [upGuardStoreResult, hgo', upRelativeStore, runBlock, execInstr, upGuardStore,
        Stmt.len, Cond.code]
  · intro hstop
    have hz : s.regs 3 = 0 := by simpa only [Cond.eval, not_not] using hstop
    have hB := Sem.block P E (a + 0 + (Stmt.code (upRelativeStore 2 11)).len + 2)
      [] { s with pc := a + 0 + (Stmt.code (upRelativeStore 2 11)).len + 2 }
      hFalse (by trivial) rfl
    apply Sem.mono hB
    intro k out hk
    obtain ⟨rfl, rfl⟩ := hk
    constructor
    · norm_num [Cond.code]
    · simp [upGuardStoreResult, hz, runBlock, upGuardStore, Stmt.len, Cond.code, Nat.add_assoc]
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
theorem upGuardStore_len : upGuardStore.len = 5 := rfl
theorem upBasedPrefixCode_noBranch : NoBranch upBasedPrefixCode := by
  change (Instr.add 5 5 6).NoBranchI ∧ NoBranch (upBasedCore ++ (upBasedWidth ++ upBasedRead))
  refine ⟨by simp [Instr.NoBranchI], (upNoBranch_append _ _).mpr ⟨upBasedCore_noBranch, ?_⟩⟩
  simp [upBasedWidth, upBasedRead, NoBranch, Instr.NoBranchI]
theorem upBasedBody_sem (P : Program) (E : RAMEnv) (a : ℕ) (s : RAMState)
    (hAt : At P a (upBasedBody.compile a)) (hOne : 1 < 2 ^ E.W) (hpc : s.pc = a) :
    Sem P E a (a + 119) s
      (fun k out => k ≤ 118 ∧ out = upBasedBodyResult E a s) := by
  have hParts := At.seqStmt (show At P a
    ((Stmt.seq (.code upBasedPrefixCode)
      (.seq upGuardStore (.code (upBasedNext ++ upBasedCount)))).compile a) from hAt)
  have hPreAt : At P a upBasedPrefixCode := hParts.1
  have hRestAt : At P (a + 107)
      ((Stmt.seq upGuardStore (.code (upBasedNext ++ upBasedCount))).compile (a + 107)) := by
    simpa only [Stmt.len, upBasedPrefixCode_length] using hParts.2
  have hRest := At.seqStmt hRestAt
  have hGuardAt : At P (a + 107) (upGuardStore.compile (a + 107)) := hRest.1
  have hEndAt : At P (a + 112) (upBasedNext ++ upBasedCount) := by
    simpa only [upGuardStore_len, Stmt.compile, Nat.add_assoc, Nat.reduceAdd] using hRest.2
  let q := runBlock upBasedPrefixCode E s
  let u := { upGuardStoreResult E q with pc := a + 112 }
  have hPre : Sem P E a (a + 107) s (fun k out => k ≤ 107 ∧ out = q) := by
    have h := Sem.block P E a upBasedPrefixCode s hPreAt upBasedPrefixCode_noBranch hpc
    refine Sem.mono (show Sem P E a (a + 107) s
      (fun k out => k = 107 ∧ out = q) from by
        simpa only [upBasedPrefixCode_length] using h) ?_
    intro k out h; exact ⟨h.1.le, h.2⟩
  have hQpc : q.pc = a + 107 := by
    change (runBlock upBasedPrefixCode E s).pc = _
    rw [runBlock_pc _ _ _ upBasedPrefixCode_noBranch, hpc, upBasedPrefixCode_length]
  have hGuard : Sem P E (a + 107) (a + 112) q (fun k out => k ≤ 4 ∧ out = u) := by
    have h := upGuardStore_sem P E (a + 107) q hGuardAt hOne hQpc
    simpa only [upGuardStore_len, Nat.add_assoc, Nat.reduceAdd] using h
  have hEnd : Sem P E (a + 112) (a + 119) u
      (fun k out => k ≤ 7 ∧ out = upBasedBodyResult E a s) := by
    have h := Sem.block P E (a + 112) (upBasedNext ++ upBasedCount) u hEndAt upBasedEnd_noBranch rfl
    have h' : Sem P E (a + 112) (a + 119) u
        (fun k out => k = 7 ∧ out = runBlock (upBasedNext ++ upBasedCount) E u) := by
      simpa only [upBasedEnd_length, Nat.add_assoc, Nat.reduceAdd] using h
    refine Sem.mono h' ?_
    intro k out hk
    exact ⟨hk.1.le, hk.2.trans (upBasedBodyResult_eq E a s).symm⟩
  have hTail := Sem.seq_bound hGuard (fun v hv hEq => by subst v; exact hEnd)
  have hFull := Sem.seq_bound hPre (fun v hv hEq => by subst v; exact hTail)
  exact hFull
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
def UpDataEq (s t : RAMState) : Prop := s.regs = t.regs ∧ s.mem = t.mem
theorem upDataEq_reset {s t : RAMState} (h : UpDataEq s t) (pc : ℕ) :
    { s with pc := pc } = { t with pc := pc } :=
  ramState_eq_of _ _ rfl h.2 (fun r => congrFun h.1 r)
theorem upExec_data_congr (E : RAMEnv) (ins : Instr) {s t : RAMState} (h : UpDataEq s t) :
    UpDataEq (execInstr ins E s) (execInstr ins E t) := by
  obtain ⟨hr, hm⟩ := h
  cases ins <;> constructor <;> simp [execInstr, hr, hm]
theorem upBlock_data_congr (E : RAMEnv) (code : List Instr) {s t : RAMState} (h : UpDataEq s t) :
    UpDataEq (runBlock code E s) (runBlock code E t) := by
  induction code generalizing s t with
  | nil => exact h
  | cons ins rest ih => exact ih (upExec_data_congr E ins h)
def upFiniteStmt : Stmt → Prop
  | .code code => NoBranch code
  | .seq left right => upFiniteStmt left ∧ upFiniteStmt right
  | .ite _ left right => upFiniteStmt left ∧ upFiniteStmt right
  | .loop _ _ => False
theorem upFiniteEval_data_congr (E : RAMEnv) (stmt : Stmt) {s t : RAMState} (h : UpDataEq s t) :
    UpDataEq (upFiniteEval E stmt s) (upFiniteEval E stmt t) := by
  induction stmt generalizing s t with
  | code code => exact upBlock_data_congr E code h
  | seq left right ihLeft ihRight => exact ihRight (ihLeft h)
  | ite c left right ihLeft ihRight =>
      have hCode := upBlock_data_congr E c.code h
      have hTest := congrFun hCode.1 c.test
      simp only [upFiniteEval]
      rw [hTest]
      split
      · exact ihRight hCode
      · exact ihLeft hCode
  | loop c body ih => exact h
theorem upFiniteEval_sem (P : Program) (E : RAMEnv) (stmt : Stmt)
    (hFinite : upFiniteStmt stmt) (hWord : 1 < 2 ^ E.W) :
    ∀ (base : ℕ) (s : RAMState), At P base (stmt.compile base) → s.pc = base →
      Sem P E base (base + stmt.len) s
        (fun k out => k ≤ stmt.len ∧ out = { upFiniteEval E stmt s with pc := base + stmt.len }) := by
  revert hFinite
  induction stmt with
  | code code =>
      intro hFinite base s hAt hpc
      refine Sem.mono (Sem.block P E base code s hAt hFinite hpc) ?_
      intro k out hk
      obtain ⟨rfl, rfl⟩ := hk
      refine ⟨le_rfl, ?_⟩
      change runBlock code E s = { runBlock code E s with pc := base + code.length }
      refine ramState_eq_of (runBlock code E s) _ ?_ rfl (fun _ => rfl)
      exact (runBlock_pc code E s hFinite).trans (by rw [hpc])
  | seq left right ihLeft ihRight =>
      intro hFinite base s hAt hpc
      have hLen : base + (Stmt.seq left right).len = base + left.len + right.len := by
        simp only [Stmt.len, Nat.add_assoc]
      rw [hLen]
      obtain ⟨hAtLeft, hAtRight⟩ := At.seqStmt hAt
      let mid : RAMState := { upFiniteEval E left s with pc := base + left.len }
      have hLeft := ihLeft hFinite.1 base s hAtLeft hpc
      have hRight := ihRight hFinite.2 (base + left.len) mid hAtRight rfl
      have hBoth := Sem.seq_bound hLeft (fun v hv hEq => by rw [hEq]; exact hRight)
      refine Sem.mono hBoth ?_
      intro k out hk
      refine ⟨hk.1, hk.2.trans ?_⟩
      have hData := upFiniteEval_data_congr E right (show UpDataEq mid (upFiniteEval E left s) from ⟨rfl, rfl⟩)
      simpa only [upFiniteEval, Stmt.len, Nat.add_assoc] using upDataEq_reset hData (base + left.len + right.len)
  | ite c left right ihLeft ihRight =>
      intro hFinite base s hAt hpc
      have hLen : base + (Stmt.ite c left right).len = base + c.code.length + left.len + right.len + 3 := by
        simp only [Stmt.len, Nat.add_assoc]
      rw [hLen]
      have hParts := at_ite hAt
      let tested := runBlock c.code E s
      apply Sem.ite P E base c left right s
        (fun k out => k ≤ (Stmt.ite c left right).len ∧
          out = { upFiniteEval E (.ite c left right) s with pc := base + c.code.length + left.len + right.len + 3 }) hAt hWord hpc
      · intro hgo
        have hNZ : tested.regs c.test ≠ 0 := (Cond.eval_iff c E s hWord).mp hgo
        let entry : RAMState := { tested with pc := base + c.code.length + 1 }
        have hBranch := ihLeft hFinite.1 (base + c.code.length + 1) entry hParts.2.2.1 rfl
        refine Sem.mono hBranch ?_
        intro k out hk
        refine ⟨?_, ?_⟩
        · change c.code.length + 1 + k + 1 ≤ c.code.length + left.len + right.len + 3
          omega
        · rw [hk.2]
          have hData := upFiniteEval_data_congr E left (show UpDataEq entry tested from ⟨rfl, rfl⟩)
          have hNZraw : (runBlock c.code E s).regs c.test ≠ 0 := hNZ
          simpa only [upFiniteEval, if_neg hNZraw, Stmt.len] using
            upDataEq_reset hData (base + c.code.length + left.len + right.len + 3)
      · intro hstop
        have hZero : tested.regs c.test = 0 := by
          by_contra hNZ
          exact hstop ((Cond.eval_iff c E s hWord).mpr hNZ)
        let entry : RAMState := { tested with pc := base + c.code.length + left.len + 2 }
        have hAtRight : At P (base + c.code.length + left.len + 2)
            (right.compile (base + c.code.length + left.len + 2)) := by
          convert hParts.2.2.2.2.1 using 1 <;> omega
        have hBranch := ihRight hFinite.2 (base + c.code.length + left.len + 2) entry hAtRight rfl
        have hBranch' : Sem P E (base + c.code.length + left.len + 2)
            (base + c.code.length + 1 + left.len + 1 + right.len) entry
            (fun k out => k ≤ right.len ∧ out =
              { upFiniteEval E right entry with pc := base + c.code.length + left.len + 2 + right.len }) := by
          convert hBranch using 1 <;> omega
        refine Sem.mono hBranch' ?_
        intro k out hk
        refine ⟨?_, ?_⟩
        · change c.code.length + 1 + k + 1 ≤ c.code.length + left.len + right.len + 3
          omega
        · rw [hk.2]
          have hData := upFiniteEval_data_congr E right (show UpDataEq entry tested from ⟨rfl, rfl⟩)
          have hZraw : (runBlock c.code E s).regs c.test = 0 := hZero
          simpa only [upFiniteEval, if_pos hZraw, Stmt.len] using
            upDataEq_reset hData (base + c.code.length + left.len + right.len + 3)
  | loop c body ih => intro hFinite; exact False.elim hFinite
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upSavedPost_len : upSavedPost.len = 23 := rfl
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
theorem upSavedPost_finite : upFiniteStmt upSavedPost := by
  simp [upFiniteStmt, upSavedPost, upSavedMode, upSavedSlot, upSavedWrite,
    upSavedRead, NoBranch, Instr.NoBranchI]
theorem upSavedPost_sem (P : Program) (E : RAMEnv) (base : ℕ) (p : RAMState)
    (hAt : At P base (upSavedPost.compile base)) (hWord : 1 < 2 ^ E.W) (hpc : p.pc = base) :
    Sem P E base (base + 23) p
      (fun k out => k ≤ 23 ∧ out = { upSavedPostRun E p with pc := base + 23 }) := by
  have h := upFiniteEval_sem P E upSavedPost upSavedPost_finite hWord base p hAt hpc
  simpa only [upSavedPost_len, ← upSavedPostRun_eq] using h
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upBasedBody_len : upBasedBody.len = 119 := rfl
theorem upSavedBody_sem (P : Program) (E : RAMEnv) (base : ℕ) (p : RAMState)
    (hAt : At P base (upSavedBody.compile base)) (hWord : 1 < 2 ^ E.W) (hpc : p.pc = base) :
    Sem P E base (base + 145) p
      (fun k out => k ≤ 144 ∧ out = upSavedBodyResult E base p) := by
  have hParts := At.seqStmt (show At P base
    ((Stmt.seq upBasedBody (.seq upSavedPost (.code upBasedCount))).compile base) from hAt)
  have hBodyAt : At P base (upBasedBody.compile base) := hParts.1
  have hRestAt : At P (base + 119) ((Stmt.seq upSavedPost (.code upBasedCount)).compile (base + 119)) := by
    simpa only [upBasedBody_len] using hParts.2
  have hRest := At.seqStmt hRestAt
  have hPostAt : At P (base + 119) (upSavedPost.compile (base + 119)) := hRest.1
  have hCountAt : At P (base + 142) upBasedCount := by
    simpa only [upSavedPost_len, Stmt.compile, Nat.add_assoc, Nat.reduceAdd] using hRest.2
  let q := upBasedBodyResult E base p
  let u : RAMState := { upSavedPostRun E q with pc := base + 142 }
  have hBody := upBasedBody_sem P E base p hBodyAt hWord hpc
  have hPost : Sem P E (base + 119) (base + 142) q
      (fun k out => k ≤ 23 ∧ out = u) := by
    have h := upSavedPost_sem P E (base + 119) q hPostAt hWord (upBasedBodyResult_meta E base p).1
    simpa only [Nat.add_assoc, Nat.reduceAdd] using h
  have hCount : Sem P E (base + 142) (base + 145) u
      (fun k out => k ≤ 3 ∧ out = upSavedBodyResult E base p) := by
    have h := Sem.block P E (base + 142) upBasedCount u hCountAt upBasedCount_noBranch rfl
    have h' : Sem P E (base + 142) (base + 145) u
        (fun k out => k = 3 ∧ out = runBlock upBasedCount E u) := by
      simpa only [upBasedCount_length, Nat.add_assoc, Nat.reduceAdd] using h
    refine Sem.mono h' ?_
    intro k out hk
    exact ⟨hk.1.le, hk.2.trans (upSavedBodyResult_eq E base p).symm⟩
  have hTail := Sem.seq_bound hPost (fun v hv hEq => by rw [hEq]; exact hCount)
  exact Sem.seq_bound hBody (fun v hv hEq => by rw [hEq]; exact hTail)
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
namespace LinearSetReconciliation327.Main
theorem upLoop_bounded (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (body : Stmt)
    (hAt : At P a ((Stmt.loop c body).compile a)) (hOne : 1 < 2 ^ E.W)
    (B : ℕ) : ∀ (n : ℕ) (states : ℕ → RAMState),
      (∀ j, (states j).pc = a) →
      (∀ j < n, c.eval (states j)) → (¬ c.eval (states n)) →
      (∀ j < n, Sem P E (a + c.code.length + 1) a
        { runBlock c.code E (states j) with pc := a + c.code.length + 1 }
        (fun k out => k ≤ B ∧ out = states (j + 1))) →
      Sem P E a (a + c.code.length + body.len + 2) (states 0)
        (fun k out => k ≤ (c.code.length + 1 + B) * n + (c.code.length + 1) ∧
          out = { runBlock c.code E (states n) with pc := a + c.code.length + body.len + 2 }) := by
  intro n
  induction n with
  | zero =>
      intro states hpc hgo hstop hbody
      refine Sem.mono (Sem.loopExit P E a c body (states 0) hAt hOne (hpc 0) hstop) ?_
      intro k out h; exact ⟨by simpa using h.1.le, h.2⟩
  | succ n ih =>
      intro states hpc hgo hstop hbody
      obtain ⟨hEntry, cost, result, hRun, hReturn, hBound, hResult⟩ := hbody 0 (by omega)
      rw [hResult] at hRun hReturn
      have hExact : Sem P E (a + c.code.length + 1) a
          { runBlock c.code E (states 0) with pc := a + c.code.length + 1 }
          (fun k out => k = cost ∧ out = states 1) :=
        ⟨hEntry, cost, states 1, hRun, hReturn, rfl, rfl⟩
      have hStep := Sem.loopStep P E a c body (states 0) (states 1) cost hAt hOne
        (hpc 0) (hgo 0 (by omega)) hExact
      have hStepBound : Sem P E a a (states 0)
          (fun k out => k ≤ c.code.length + 1 + B ∧ out = states 1) := by
        refine Sem.mono hStep ?_
        intro k out h; exact ⟨by omega, h.2⟩
      have hRest := ih (fun j => states (j + 1)) (fun j => hpc (j + 1))
        (fun j hj => hgo (j + 1) (by omega)) (by simpa using hstop)
        (fun j hj => hbody (j + 1) (by omega))
      have hFull := Sem.seq_bound hStepBound (fun v hv hEq => by subst v; exact hRest)
      refine Sem.mono hFull ?_
      intro k out h
      refine ⟨?_, h.2⟩
      rw [Nat.mul_succ]
      omega
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upSavedBody_len : upSavedBody.len = 145 := rfl
theorem upSavedLoopState_pc (E : RAMEnv) (head : ℕ) (seed : RAMState) (hpc : seed.pc = head) :
    ∀ j, (upSavedLoopState E head seed j).pc = head := by
  intro j
  cases j with
  | zero => exact hpc
  | succ j => exact (upSavedLoopStep_meta E head _).1
theorem upSavedLoop_sem (P : Program) (E : RAMEnv) (head beta L : ℕ) (seed : RAMState)
    (hAt : At P head ((Stmt.loop upBasedTest upSavedBody).compile head))
    (hOne : 1 < 2 ^ E.W) (hpc : seed.pc = head) (hSeed : UpSavedReady beta L 0 seed)
    (hL : L < 2 ^ E.W) (hCount : E.det (beta % 2 ^ E.W) % 2 ^ E.W = L) :
    Sem P E head (head + 148) seed
      (fun k out => k ≤ 147 * L + 2 ∧
        out = { runBlock upBasedTest.code E (upSavedLoopState E head seed L) with pc := head + 148 }) := by
  have hParts := at_loop hAt
  have hBodyAt : At P (head + 2) (upSavedBody.compile (head + 2)) := by
    simpa only [upBasedTest, Cond.code, List.length_singleton, Nat.add_assoc, Nat.reduceAdd] using hParts.2.2.1
  have hJump : P[head + 147]? = some (Instr.jmp head) := by
    simpa only [upBasedTest, Cond.code, List.length_singleton, upSavedBody_len,
      Nat.add_assoc, Nat.reduceAdd] using hParts.2.2.2
  have hReady := upSavedLoopState_ready E head beta L seed hSeed hL hCount
  have hGo : ∀ j < L, upBasedTest.eval (upSavedLoopState E head seed j) := by
    intro j hj
    change (upSavedLoopState E head seed j).regs 5 < (upSavedLoopState E head seed j).regs 1
    rw [(hReady j hj.le).counter, (hReady j hj.le).count]
    exact hj
  have hStop : ¬ upBasedTest.eval (upSavedLoopState E head seed L) := by
    change ¬ (upSavedLoopState E head seed L).regs 5 < (upSavedLoopState E head seed L).regs 1
    rw [(hReady L le_rfl).counter, (hReady L le_rfl).count]
    exact Nat.lt_irrefl L
  have hBody : ∀ j < L, Sem P E (head + 2) head
      { runBlock upBasedTest.code E (upSavedLoopState E head seed j) with pc := head + 2 }
      (fun k out => k ≤ 145 ∧ out = upSavedLoopState E head seed (j + 1)) := by
    intro j hj
    let entry : RAMState := { runBlock upBasedTest.code E (upSavedLoopState E head seed j) with pc := head + 2 }
    have hExec : Sem P E (head + 2) (head + 147) entry
        (fun k out => k ≤ 144 ∧ out = upSavedBodyResult E (head + 2) entry) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using upSavedBody_sem P E (head + 2) entry hBodyAt hOne rfl
    apply Sem.jmp_append hJump
    refine Sem.mono hExec ?_
    intro k out hk
    refine ⟨by omega, ?_⟩
    rw [hk.2, upSavedLoopState_succ, upSavedLoopStep_eq]
  have hLoop := upLoop_bounded P E head upBasedTest upSavedBody hAt hOne 145 L
    (upSavedLoopState E head seed) (upSavedLoopState_pc E head seed hpc) hGo hStop (by
      simpa only [upBasedTest, Cond.code, List.length_singleton, Nat.add_assoc, Nat.reduceAdd] using hBody)
  simpa only [upBasedTest, Cond.code, List.length_singleton, upSavedBody_len,
    upSavedLoopState_zero, Nat.add_assoc, Nat.reduceAdd] using hLoop
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
def upBasedPrologue : List Instr :=
  [.imm 6 1, .imm 5 0, .imm 7 8, .imm 8 0, .imm 9 1] ++ upBasedCount
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
def upBasedPrologueRun (E : RAMEnv) (s : RAMState) : RAMState := runBlock upBasedPrologue E s
theorem upBasedPrologueRun_eq (E : RAMEnv) (s : RAMState) :
    upBasedPrologueRun E s = runBlock upBasedPrologue E s := by unfold upBasedPrologueRun <;> rfl
attribute [irreducible] upBasedPrologueRun
theorem upBasedPrologue_meta (E : RAMEnv) (s : RAMState)
    (hOne : 1 < 2 ^ E.W) (hEight : 8 < 2 ^ E.W) :
    (upBasedPrologueRun E s).pc = s.pc + 8 ∧
      (upBasedPrologueRun E s).regs 5 = 0 ∧ (upBasedPrologueRun E s).regs 6 = 1 ∧
      (upBasedPrologueRun E s).regs 7 = 8 ∧ (upBasedPrologueRun E s).regs 8 = 0 ∧
      (upBasedPrologueRun E s).regs 9 = 1 ∧
      (upBasedPrologueRun E s).regs 1 = E.det (s.regs 14 % 2 ^ E.W) % 2 ^ E.W ∧
      (upBasedPrologueRun E s).mem = s.mem ∧
      (∀ r, r = 0 ∨ r = 14 ∨ r = 15 → (upBasedPrologueRun E s).regs r = s.regs r) := by
  rw [upBasedPrologueRun_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp [upBasedPrologue, upBasedCount, runBlock, execInstr, Nat.add_assoc]
  · simp [upBasedPrologue, upBasedCount, runBlock, execInstr, Function.update_apply]
  · simp [upBasedPrologue, upBasedCount, runBlock, execInstr, Function.update_apply, Nat.mod_eq_of_lt hOne]
  · simp [upBasedPrologue, upBasedCount, runBlock, execInstr, Function.update_apply, Nat.mod_eq_of_lt hEight]
  · simp [upBasedPrologue, upBasedCount, runBlock, execInstr, Function.update_apply]
  · simp [upBasedPrologue, upBasedCount, runBlock, execInstr, Function.update_apply, Nat.mod_eq_of_lt hOne]
  · simp [upBasedPrologue, upBasedCount, runBlock, execInstr, Function.update_apply]
  · intro r hr
    rcases hr with rfl | rfl | rfl <;>
      exact upBlock_register_frame _ E s _ (by simp [upBasedPrologue, upBasedCount, upRegTarget])
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
namespace LinearSetReconciliation327.Main
def upSavedSup : Stmt := .seq (.code upBasedPrologue) (.loop upBasedTest upSavedBody)
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upBasedPrologue_length : upBasedPrologue.length = 8 := rfl
theorem upBasedPrologue_noBranch : NoBranch upBasedPrologue := by
  simp [upBasedPrologue, upBasedCount, NoBranch, Instr.NoBranchI]
def upSavedSupResult (E : RAMEnv) (base : ℕ) (s : RAMState) (L : ℕ) : RAMState :=
  { runBlock upBasedTest.code E
      (upSavedLoopState E (base + 8) (upBasedPrologueRun E s) L) with pc := base + 156 }
theorem upSavedSupResult_eq (E : RAMEnv) (base : ℕ) (s : RAMState) (L : ℕ) :
    upSavedSupResult E base s L =
      { runBlock upBasedTest.code E
        (upSavedLoopState E (base + 8) (upBasedPrologueRun E s) L) with pc := base + 156 } := by unfold upSavedSupResult <;> rfl
attribute [irreducible] upSavedSupResult
theorem upSavedSup_sem (P : Program) (E : RAMEnv) (base L : ℕ) (s : RAMState)
    (hAt : At P base (upSavedSup.compile base))
    (hOne : 1 < 2 ^ E.W) (hEight : 8 < 2 ^ E.W)
    (hL : L < 2 ^ E.W) (hCount : E.det (s.regs 14 % 2 ^ E.W) % 2 ^ E.W = L)
    (hpc : s.pc = base) :
    Sem P E base (base + 156) s
      (fun k out => k ≤ 147 * L + 10 ∧ out = upSavedSupResult E base s L ∧
        out.regs 0 = s.regs 0 ∧ out.regs 14 = s.regs 14 ∧ out.regs 15 = s.regs 15) := by
  have hParts := At.seqStmt (show At P base
    ((Stmt.seq (.code upBasedPrologue) (.loop upBasedTest upSavedBody)).compile base) from hAt)
  have hPreAt : At P base upBasedPrologue := hParts.1
  have hLoopAt : At P (base + 8)
      ((Stmt.loop upBasedTest upSavedBody).compile (base + 8)) := by
    simpa only [Stmt.len, upBasedPrologue_length] using hParts.2
  let seed := upBasedPrologueRun E s
  obtain ⟨hPpc, hP5, hP6, hP7, hP8, hP9, hP1, hPm, hPfr⟩ := upBasedPrologue_meta E s hOne hEight
  have hSeedPc : seed.pc = base + 8 := by rw [hPpc, hpc]
  have hSeed : UpSavedReady (s.regs 14) L 0 seed :=
    ⟨hP5, hP6, hP1.trans hCount, hPfr 14 (Or.inr (Or.inl rfl))⟩
  have hPre : Sem P E base (base + 8) s (fun k out => k ≤ 8 ∧ out = seed) := by
    have h := Sem.block P E base upBasedPrologue s hPreAt upBasedPrologue_noBranch hpc
    have h' : Sem P E base (base + 8) s (fun k out => k = 8 ∧ out = seed) := by
      simpa only [upBasedPrologue_length, ← upBasedPrologueRun_eq] using h
    exact Sem.mono h' (fun _ _ h => ⟨h.1.le, h.2⟩)
  have hLoop : Sem P E (base + 8) (base + 156) seed
      (fun k out => k ≤ 147 * L + 2 ∧ out = upSavedSupResult E base s L) := by
    have h := upSavedLoop_sem P E (base + 8) (s.regs 14) L seed hLoopAt hOne hSeedPc hSeed hL hCount
    simpa only [upSavedSupResult_eq, Nat.add_assoc, Nat.reduceAdd] using h
  have hFull := Sem.seq_bound hPre (fun v hv hEq => by subst v; exact hLoop)
  refine Sem.mono hFull ?_
  intro k out hk
  refine ⟨by omega, hk.2, ?_, ?_, ?_⟩
  all_goals
    rw [hk.2, upSavedSupResult_eq]
    first
    | exact (upBasedTest_frame E _ 0 (by decide)).trans
        ((upSavedLoopState_frame E (base + 8) seed 0 (Or.inl rfl) L).trans (hPfr 0 (Or.inl rfl)))
    | exact (upBasedTest_frame E _ 14 (by decide)).trans
        ((upSavedLoopState_frame E (base + 8) seed 14 (Or.inr (Or.inl rfl)) L).trans (hPfr 14 (Or.inr (Or.inl rfl))))
    | exact (upBasedTest_frame E _ 15 (by decide)).trans
        ((upSavedLoopState_frame E (base + 8) seed 15 (Or.inr (Or.inr rfl)) L).trans (hPfr 15 (Or.inr (Or.inr rfl))))
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem upSavedSup_fold_sem (P : Program) (E : RAMEnv) (hNative : UpSavedItemSemantics E)
    (base betaDet betaPay i words : ℕ) (items : List UpIt) (s : RAMState) (ab : UpAbs)
    (hAt : At P base (upSavedSup.compile base)) (hpc : s.pc = base)
    (hLayout : UpSavedLayout E betaDet items)
    (hMem : upVirtualMem E.W betaPay s.mem = ab.mem) (hc0 : ab.c = 0) (hf1 : ab.f = 1)
    (hRaw : UpBasedRawPayload betaPay words ab s)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + words ≤ 2 ^ E.W)
    (h16 : 16 < 2 ^ E.W) (h0 : s.regs 0 = i) (h14 : s.regs 14 = betaDet) (h15 : s.regs 15 = betaPay)
    (hCount : E.det (betaDet % 2 ^ E.W) % 2 ^ E.W = items.length)
    (hSafe : ∀ (j : ℕ) (hj : j < items.length),
      let a := upFold (upShiftDetEnv E betaDet) i ab (items.take j)
      upvMask (upShiftDetEnv E betaDet) i (items[j]'hj) a ≠ 0 →
        upvWi (upShiftDetEnv E betaDet) i (items[j]'hj) a < words) :
    Sem P E base (base + 156) s
      (fun k out => k ≤ 147 * items.length + 10 ∧
        UpBasedView E.W betaPay (upFold (upShiftDetEnv E betaDet) i ab items) out ∧
        UpBasedRawPayload betaPay words (upFold (upShiftDetEnv E betaDet) i ab items) out ∧
        UpMemFrame (UpSavedAllowed E.W betaPay words items) s out ∧
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
  have hFold := upSavedLoopState_effect E hNative (base + 8) betaDet betaPay i words items seed ab
    hLayout hSeedView hSeedRaw hPay hEnd h16 (by rw [hc0]; exact Nat.two_pow_pos E.W)
    (by rw [hf1]; exact hW) hSeedReady hP7 ((hPfr 0 (by tauto)).trans h0)
    ((hPfr 15 (by tauto)).trans h15) hCount hSafe items.length le_rfl
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
    exact hFold.2.1 q hq
  have hResultFrame : UpMemFrame (UpSavedAllowed E.W betaPay words items) s
      (upSavedSupResult E base s items.length) := by
    intro addr hOutside
    rw [upSavedSupResult_eq, upBasedTest_mem]
    exact (hFold.2.2 addr hOutside).trans (congrFun hPm addr)
  have hExec := upSavedSup_sem P E base items.length s hAt hW h8 hL
    (by rw [h14]; exact hCount) hpc
  apply Sem.mono hExec
  intro k out hk
  refine ⟨hk.1, ?_, ?_, ?_, hk.2.2.1, hk.2.2.2.1.trans h14, hk.2.2.2.2.trans h15⟩
  · rw [hk.2.1]
    exact hResultView
  · rw [hk.2.1]
    exact hResultRaw
  · rw [hk.2.1]
    exact hResultFrame

end LinearSetReconciliation327.Main



namespace LinearSetReconciliation327.Main
theorem upSavedSup_native_fold_sem (P : Program) (E : RAMEnv)
    (base betaDet betaPay i words : ℕ) (items : List UpIt) (s : RAMState) (ab : UpAbs)
    (hAt : At P base (upSavedSup.compile base)) (hpc : s.pc = base)
    (hLayout : UpSavedLayout E betaDet items)
    (hMem : upVirtualMem E.W betaPay s.mem = ab.mem) (hc0 : ab.c = 0) (hf1 : ab.f = 1)
    (hRaw : UpBasedRawPayload betaPay words ab s)
    (hPay : betaPay < 2 ^ E.W) (hEnd : betaPay + words ≤ 2 ^ E.W)
    (h16 : 16 < 2 ^ E.W) (h0 : s.regs 0 = i) (h14 : s.regs 14 = betaDet) (h15 : s.regs 15 = betaPay)
    (hCount : E.det (betaDet % 2 ^ E.W) % 2 ^ E.W = items.length)
    (hSafe : ∀ (j : ℕ) (hj : j < items.length),
      let a := upFold (upShiftDetEnv E betaDet) i ab (items.take j)
      upvMask (upShiftDetEnv E betaDet) i (items[j]'hj) a ≠ 0 →
        upvWi (upShiftDetEnv E betaDet) i (items[j]'hj) a < words) :
    Sem P E base (base + 156) s
      (fun k out => k ≤ 147 * items.length + 10 ∧
        UpBasedView E.W betaPay (upFold (upShiftDetEnv E betaDet) i ab items) out ∧
        UpBasedRawPayload betaPay words (upFold (upShiftDetEnv E betaDet) i ab items) out ∧
        UpMemFrame (UpSavedAllowed E.W betaPay words items) s out ∧
        out.regs 0 = s.regs 0 ∧ out.regs 14 = betaDet ∧ out.regs 15 = betaPay) := by
  exact upSavedSup_fold_sem P E (upSavedBody_effect E) base betaDet betaPay i words items s ab
    hAt hpc hLayout hMem hc0 hf1 hRaw hPay hEnd h16 h0 h14 h15 hCount hSafe
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.upSavedSup_native_fold_sem


