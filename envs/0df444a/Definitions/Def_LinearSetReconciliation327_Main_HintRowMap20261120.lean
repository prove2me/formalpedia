-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowMap20261120
-- name    : LinearSetReconciliation327_Main_HintRowMap20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:55:40.624926+00:00
-- url     : https://prove2.me/theorems/12a47243-4a56-41f6-8dfd-39eef5f55a83
-- title:
--   LinearSetReconciliation327 — HintRowMap (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowMap20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowMatVec20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintRowMatrix20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDenseMatrix {a h : ℕ} (F : HintVec h →ₗ[ZMod 2] HintVec a) (r t : ℕ) : ZMod 2 :=
  if hr : r < a then hintDenseRow F ⟨r, hr⟩ t else 0

theorem hintMatVecProduct_dense {a h : ℕ} (F : HintVec h →ₗ[ZMod 2] HintVec a)
    (v : HintVec h) (r : Fin a) :
    hintMatVecProduct h (hintDenseMatrix F) (hintDenseVec v) r.val = F v r := by
  have hRow : hintDenseMatrix F r.val = hintDenseRow F r := by
    funext t
    simp only [hintDenseMatrix, dif_pos r.isLt]
  rw [hintMatVecProduct, hRow]
  exact hintDotSum_dense F v r

/-- The complete native matrix loop computes the abstract linear map, including
    its time bound and its exact external memory frame. -/
theorem hintMatVecStmt_map_sem {a h : ℕ} (F : HintVec h →ₗ[ZMod 2] HintVec a) (v : HintVec h)
    (P : Program) (E : RAMEnv) (state : RAMState) (matrix vec output base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hWidth : h < 2 ^ E.W) (hRows : a < 2 ^ E.W)
    (hMatrixSpan : matrix + a * h < 2 ^ E.W) (hVecSpan : vec + h < 2 ^ E.W)
    (hOutSpan : output + a < 2 ^ E.W)
    (hMatrix : ∀ r : Fin a, ∀ t : Fin h,
      state.mem (matrix + r.val * h + t.val) = (F (Pi.single t 1) r).val)
    (hVector : ∀ t : Fin h, state.mem (vec + t.val) = (v t).val)
    (hMatrixSeparate : matrix + a * h ≤ output ∨ output + a ≤ matrix)
    (hVecSeparate : vec + h ≤ output ∨ output + a ≤ vec)
    (hAt : At P base (hintMatVecStmt.compile base)) (hPc : state.pc = base)
    (hSetup : HintMatVecSetup matrix vec output h a state) :
    Sem P E base (base + 21) state (fun k out => k ≤ (11 * h + 11) * a + 3 ∧
      (∀ r : Fin a, out.mem (output + r.val) = (F v r).val) ∧
      (∀ addr, (addr < output ∨ output + a ≤ addr) → out.mem addr = state.mem addr) ∧
      HintMatVecArgs matrix vec output h a a out ∧ out.regs 14 = state.regs 14) := by
  have hMatrix' : ∀ r < a, ∀ t < h,
      state.mem (matrix + r * h + t) = (hintDenseMatrix F r t).val := by
    intro r hr t ht
    simpa only [hintDenseMatrix, hintDenseRow, dif_pos hr, dif_pos ht] using hMatrix ⟨r, hr⟩ ⟨t, ht⟩
  have hVector' : ∀ t < h, state.mem (vec + t) = (hintDenseVec v t).val := by
    intro t ht
    simpa only [hintDenseVec, dif_pos ht] using hVector ⟨t, ht⟩
  have hNative := hintMatVecStmt_sem P E state matrix vec output h a base
    (hintDenseMatrix F) (hintDenseVec v) hWord hWidth hRows hMatrixSpan hVecSpan hOutSpan
    hMatrix' hVector' hMatrixSeparate hVecSeparate hAt hPc hSetup
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hK, _, hValue, hFrame, hArgs, h14⟩ := hOut
  refine ⟨hK, ?_, hFrame, hArgs, h14⟩
  intro r
  simpa only [hintMatVecProduct_dense] using hValue r.val r.isLt

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintMatVecStmt_map_sem


