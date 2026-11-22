-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintGaussUpdate20261120
-- name    : LinearSetReconciliation327_Main_HintGaussUpdate20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:58:21.211591+00:00
-- url     : https://prove2.me/theorems/c4a06aa0-9635-4f66-b4aa-9cb731e6ad47
-- title:
--   LinearSetReconciliation327 — HintGaussUpdate (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintGaussUpdate20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowRank20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintRowMap20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintRowMatrix20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- The whole native rank-one matrix loop performs the residual update of
    one Gaussian insertion, with the old pivot row cached separately. -/
theorem hintRankOneStmt_residual_sem {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (B : HintElimState a h) (j : Fin h) (pivot : Fin a)
    (P : Program) (E : RAMEnv) (state : RAMState) (matrix cache scales base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hWidth : a < 2 ^ E.W) (hRows : a < 2 ^ E.W)
    (hMatrixSpan : matrix + a * a < 2 ^ E.W) (hCacheSpan : cache + a < 2 ^ E.W)
    (hScaleSpan : scales + a < 2 ^ E.W)
    (hMatrix : ∀ r : Fin a, ∀ t : Fin a,
      state.mem (matrix + r.val * a + t.val) = (B.residual (Pi.single t 1) r).val)
    (hCache : ∀ t : Fin a, state.mem (cache + t.val) = (B.residual (Pi.single t 1) pivot).val)
    (hScale : ∀ r : Fin a, state.mem (scales + r.val) = (B.residual (A (Pi.single j 1)) r).val)
    (hSeparate : matrix + a * a ≤ cache ∨ cache + a ≤ matrix)
    (hScaleSeparate : matrix + a * a ≤ scales ∨ scales + a ≤ matrix)
    (hAt : At P base (hintRankOneStmt.compile base)) (hPc : state.pc = base)
    (hSetup : HintRankOneSetup matrix cache scales a a state) :
    Sem P E base (base + 21) state (fun k out => k ≤ (11 * a + 11) * a + 3 ∧
      (∀ r : Fin a, ∀ t : Fin a,
        out.mem (matrix + r.val * a + t.val) = ((hintElimInsert A B j pivot).residual (Pi.single t 1) r).val) ∧
      CRMemFrame matrix (matrix + a * a) state.mem out.mem ∧
      HintRankOneArgs matrix cache scales a a a out ∧ out.regs 14 = state.regs 14) := by
  have hMatrix' : ∀ r < a, ∀ t < a,
      state.mem (matrix + r * a + t) = (hintDenseMatrix B.residual r t).val := by
    intro r hr t ht
    simpa only [hintDenseMatrix, hintDenseRow, dif_pos hr, dif_pos ht] using hMatrix ⟨r, hr⟩ ⟨t, ht⟩
  have hCache' : ∀ t < a, state.mem (cache + t) = (hintDenseRow B.residual pivot t).val := by
    intro t ht
    simpa only [hintDenseRow, dif_pos ht] using hCache ⟨t, ht⟩
  have hScale' : ∀ r < a, state.mem (scales + r) = (hintDenseVec (B.residual (A (Pi.single j 1))) r).val := by
    intro r hr
    simpa only [hintDenseVec, dif_pos hr] using hScale ⟨r, hr⟩
  have hNative := hintRankOneStmt_sem P E state matrix cache scales a a base
    (hintDenseVec (B.residual (A (Pi.single j 1)))) (hintDenseMatrix B.residual) (hintDenseRow B.residual pivot)
    hWord hWidth hRows hMatrixSpan hCacheSpan hScaleSpan hMatrix' hCache' hScale'
    hSeparate hScaleSeparate hAt hPc hSetup
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hK, hCells, hFrame, hArgs, h14⟩ := hOut
  refine ⟨hK, ?_, hFrame, hArgs, h14⟩
  intro r t
  rw [hintElimInsert_residual_coefficient]
  simpa only [hintDenseMatrix, hintDenseRow, hintDenseVec, dif_pos r.isLt, dif_pos t.isLt] using
    hCells r.val r.isLt t.val t.isLt

/-- The whole native rank-one matrix loop performs the lift update of
    one Gaussian insertion, with the old pivot row cached separately. -/
theorem hintRankOneStmt_lift_sem {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (B : HintElimState a h) (j : Fin h) (pivot : Fin a)
    (P : Program) (E : RAMEnv) (state : RAMState) (matrix cache scales base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hWidth : a < 2 ^ E.W) (hRows : h < 2 ^ E.W)
    (hMatrixSpan : matrix + h * a < 2 ^ E.W) (hCacheSpan : cache + a < 2 ^ E.W)
    (hScaleSpan : scales + h < 2 ^ E.W)
    (hMatrix : ∀ r : Fin h, ∀ t : Fin a,
      state.mem (matrix + r.val * a + t.val) = (B.lift (Pi.single t 1) r).val)
    (hCache : ∀ t : Fin a, state.mem (cache + t.val) = (B.residual (Pi.single t 1) pivot).val)
    (hScale : ∀ r : Fin h, state.mem (scales + r.val) = (hintElimKernel A B j r).val)
    (hSeparate : matrix + h * a ≤ cache ∨ cache + a ≤ matrix)
    (hScaleSeparate : matrix + h * a ≤ scales ∨ scales + h ≤ matrix)
    (hAt : At P base (hintRankOneStmt.compile base)) (hPc : state.pc = base)
    (hSetup : HintRankOneSetup matrix cache scales a h state) :
    Sem P E base (base + 21) state (fun k out => k ≤ (11 * a + 11) * h + 3 ∧
      (∀ r : Fin h, ∀ t : Fin a,
        out.mem (matrix + r.val * a + t.val) = ((hintElimInsert A B j pivot).lift (Pi.single t 1) r).val) ∧
      CRMemFrame matrix (matrix + h * a) state.mem out.mem ∧
      HintRankOneArgs matrix cache scales a h h out ∧ out.regs 14 = state.regs 14) := by
  have hMatrix' : ∀ r < h, ∀ t < a,
      state.mem (matrix + r * a + t) = (hintDenseMatrix B.lift r t).val := by
    intro r hr t ht
    simpa only [hintDenseMatrix, hintDenseRow, dif_pos hr, dif_pos ht] using hMatrix ⟨r, hr⟩ ⟨t, ht⟩
  have hCache' : ∀ t < a, state.mem (cache + t) = (hintDenseRow B.residual pivot t).val := by
    intro t ht
    simpa only [hintDenseRow, dif_pos ht] using hCache ⟨t, ht⟩
  have hScale' : ∀ r < h, state.mem (scales + r) = (hintDenseVec (hintElimKernel A B j) r).val := by
    intro r hr
    simpa only [hintDenseVec, dif_pos hr] using hScale ⟨r, hr⟩
  have hNative := hintRankOneStmt_sem P E state matrix cache scales a h base
    (hintDenseVec (hintElimKernel A B j)) (hintDenseMatrix B.lift) (hintDenseRow B.residual pivot)
    hWord hWidth hRows hMatrixSpan hCacheSpan hScaleSpan hMatrix' hCache' hScale'
    hSeparate hScaleSeparate hAt hPc hSetup
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hK, hCells, hFrame, hArgs, h14⟩ := hOut
  refine ⟨hK, ?_, hFrame, hArgs, h14⟩
  intro r t
  rw [hintElimInsert_lift_coefficient]
  simpa only [hintDenseMatrix, hintDenseRow, hintDenseVec, dif_pos r.isLt, dif_pos t.isLt] using
    hCells r.val r.isLt t.val t.isLt

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRankOneStmt_residual_sem
#print axioms LinearSetReconciliation327.Main.hintRankOneStmt_lift_sem

namespace LinearSetReconciliation327.Main

def hintUnitCode : List Instr := [.add 3 4 0, .load 9 3, .bxor 9 9 15, .store 3 9]
def hintUnitStmt : Stmt := .code hintUnitCode

def hintUnitResult (state : RAMState) (dest index : ℕ) (value : ZMod 2) : RAMState :=
  {state with
    pc := state.pc + 4
    regs := Function.update (Function.update state.regs 3 (dest + index)) 9 (value + 1).val
    mem := Function.update state.mem (dest + index) (value + 1).val}

theorem hintUnitCode_spec (E : RAMEnv) (state : RAMState) (dest index : ℕ) (value : ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hAddr : dest + index < 2 ^ E.W)
    (hDest : state.regs 4 = dest) (hIndex : state.regs 0 = index) (hOne : state.regs 15 = 1)
    (hValue : state.mem (dest + index) = value.val) :
    runBlock hintUnitCode E state = hintUnitResult state dest index value := by
  have hBit : value.val < 2 ^ E.W := (ZMod.val_lt value).trans_le hWord
  have hFlip : (value + 1).val < 2 ^ E.W := (ZMod.val_lt (value + 1)).trans_le hWord
  have hXor : value.val ^^^ 1 = (value + 1).val := by
    simpa only [show (1 : ZMod 2).val = 1 from rfl] using hintBit_xor value 1
  apply crState_ext
  · simp [hintUnitCode, hintUnitResult, runBlock, execInstr, Nat.add_assoc]
  · funext r
    simp [hintUnitCode, hintUnitResult, runBlock, execInstr, hDest, hIndex, hOne, hValue,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hBit, hXor, Nat.mod_eq_of_lt hFlip]
  · simp [hintUnitCode, hintUnitResult, runBlock, execInstr, hDest, hIndex, hOne, hValue,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hBit, hXor, Nat.mod_eq_of_lt hFlip]

theorem hintUnitStmt_sem {h : ℕ} (v : HintVec h) (j : Fin h)
    (P : Program) (E : RAMEnv) (state : RAMState) (dest base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hAddr : dest + j.val < 2 ^ E.W)
    (hDest : state.regs 4 = dest) (hIndex : state.regs 0 = j.val) (hOne : state.regs 15 = 1)
    (hVector : ∀ t : Fin h, state.mem (dest + t.val) = (v t).val)
    (hAt : At P base (hintUnitStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 4) state (fun k out => k = 4 ∧
      (∀ t : Fin h, out.mem (dest + t.val) = ((v + (Pi.single j 1 : HintVec h)) t).val) ∧
      (∀ addr, addr ≠ dest + j.val → out.mem addr = state.mem addr) ∧
      (∀ r, r ≠ 3 → r ≠ 9 → out.regs r = state.regs r)) := by
  have hSpec := hintUnitCode_spec E state dest j.val (v j) hWord hAddr hDest hIndex hOne (hVector j)
  let out := hintUnitResult state dest j.val (v j)
  have hRun : (step P E)^[4] state = out := by
    have hAt' : At P state.pc hintUnitCode := by rw [hPc]; exact hAt
    have hh := iterate_runBlock_of_at P E hintUnitCode state hAt'
      (by simp [hintUnitCode, NoBranch, Instr.NoBranchI])
    simpa only [show hintUnitCode.length = 4 from rfl, hSpec] using hh
  refine ⟨hPc, 4, out, hRun, ?_, rfl, ?_, ?_, ?_⟩
  · change state.pc + 4 = base + 4
    rw [hPc]
  · intro t
    change Function.update state.mem (dest + j.val) (v j + 1).val (dest + t.val) = _
    by_cases ht : t = j
    · subst t
      simp only [Function.update_self, Pi.add_apply, Pi.single_eq_same]
    · have hNe : dest + t.val ≠ dest + j.val := by
        intro hEq
        exact ht (Fin.ext (Nat.add_left_cancel hEq))
      rw [Function.update_of_ne hNe, hVector]
      simp [Pi.single_apply, ht, Ne.symm ht]
  · intro addr hNe
    exact Function.update_of_ne hNe _ _
  · intro r h3 h9
    simp only [out, hintUnitResult, Function.update_of_ne h9, Function.update_of_ne h3]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintUnitStmt_sem


