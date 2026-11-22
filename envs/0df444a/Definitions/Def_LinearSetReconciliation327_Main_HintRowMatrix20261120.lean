-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowMatrix20261120
-- name    : LinearSetReconciliation327_Main_HintRowMatrix20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:38:32.028805+00:00
-- url     : https://prove2.me/theorems/1d4b7fec-45a6-435e-bb59-1f544ab61969
-- title:
--   LinearSetReconciliation327 — HintRowMatrix (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowMatrix20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowSolve20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintRowOps20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDenseRow {a h : ℕ} (F : HintVec h →ₗ[ZMod 2] HintVec a) (s : Fin a) (t : ℕ) : ZMod 2 :=
  if ht : t < h then F (Pi.single ⟨t, ht⟩ 1) s else 0

def hintDenseVec {h : ℕ} (v : HintVec h) (t : ℕ) : ZMod 2 := if ht : t < h then v ⟨t, ht⟩ else 0

theorem hintLinearMap_coordinate {a h : ℕ} (F : HintVec h →ₗ[ZMod 2] HintVec a)
    (v : HintVec h) (s : Fin a) :
    F v s = ∑ t : Fin h, v t * F (Pi.single t 1) s := by
  classical
  have hExpand : F v = ∑ t : Fin h, v t • F (Pi.single t 1) := by
    calc
      F v = F (∑ t : Fin h, v t • Pi.single t 1) := congrArg F (hintVec_expand v)
      _ = _ := by simp only [map_sum, map_smul]
  have hh := congrFun hExpand s
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh

theorem hintDotSum_fin (f g : ℕ → ZMod 2) (h : ℕ) :
    hintDotSum f g h = ∑ t : Fin h, f t.val * g t.val := by
  classical
  unfold hintDotSum
  refine Finset.sum_bij (fun i hi => (⟨i, Finset.mem_range.mp hi⟩ : Fin h)) ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_univ _
  · intro i _ j _ hij
    exact congrArg Fin.val hij
  · intro t _
    exact ⟨t.val, Finset.mem_range.mpr t.isLt, rfl⟩
  · intro i _
    rfl

theorem hintDotSum_dense {a h : ℕ} (F : HintVec h →ₗ[ZMod 2] HintVec a) (v : HintVec h) (s : Fin a) :
    hintDotSum (hintDenseRow F s) (hintDenseVec v) h = F v s := by
  rw [hintDotSum_fin]
  simpa only [hintDenseRow, hintDenseVec, dif_pos (Fin.isLt _), mul_comm] using
    (hintLinearMap_coordinate F v s).symm

theorem hintElimInsert_residual_coefficient {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (B : HintElimState a h) (j : Fin h) (p s t : Fin a) :
    (hintElimInsert A B j p).residual (Pi.single t 1) s =
      B.residual (Pi.single t 1) s + B.residual (A (Pi.single j 1)) s * B.residual (Pi.single t 1) p := by
  rw [hintElimInsert_residual]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem hintElimInsert_lift_coefficient {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (B : HintElimState a h) (j u : Fin h) (p t : Fin a) :
    (hintElimInsert A B j p).lift (Pi.single t 1) u =
      B.lift (Pi.single t 1) u + hintElimKernel A B j u * B.residual (Pi.single t 1) p := by
  rw [hintElimInsert_lift]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- The actual RAM dot product computes a coordinate of the abstract linear map
    when its memory contains that map's matrix row and the input vector. -/
theorem hintDotStmt_matrix_sem {a h : ℕ} (F : HintVec h →ₗ[ZMod 2] HintVec a) (v : HintVec h) (s : Fin a)
    (P : Program) (E : RAMEnv) (state : RAMState) (vec mat stride base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : h < 2 ^ E.W)
    (hVec : ∀ j < h, vec + j < 2 ^ E.W) (hMat : ∀ j < h, mat + j * stride < 2 ^ E.W)
    (hF : ∀ t : Fin h, state.mem (mat + t.val * stride) = (F (Pi.single t 1) s).val)
    (hG : ∀ t : Fin h, state.mem (vec + t.val) = (v t).val)
    (hAt : At P base (hintDotStmt.compile base)) (hPc : state.pc = base)
    (hParams : HintDotParams vec mat h stride state) :
    Sem P E base (base + 13) state (fun k out => k = 11 * h + 4 ∧
      out.regs 1 = (F v s).val ∧ out.mem = state.mem ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = state.regs r)) := by
  have hMatrix : ∀ t < h, state.mem (mat + t * stride) = (hintDenseRow F s t).val := by
    intro t ht
    simpa only [hintDenseRow, dif_pos ht] using hF ⟨t, ht⟩
  have hVector : ∀ t < h, state.mem (vec + t) = (hintDenseVec v t).val := by
    intro t ht
    simpa only [hintDenseVec, dif_pos ht] using hG ⟨t, ht⟩
  have hDot := hintDotStmt_sem P E state vec mat h stride base (hintDenseRow F s) (hintDenseVec v)
    hWord hCount hVec hMat hMatrix hVector hAt hPc hParams
  apply Sem.mono hDot
  intro k out hOut
  obtain ⟨hK, _, hValue, hMem, _, hFrame⟩ := hOut
  rw [hintDotSum_dense] at hValue
  exact ⟨hK, hValue, hMem, hFrame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDotStmt_matrix_sem


