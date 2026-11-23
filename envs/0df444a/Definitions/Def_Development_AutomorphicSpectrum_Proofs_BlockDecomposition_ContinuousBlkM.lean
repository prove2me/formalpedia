-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:00.329126+00:00
-- url     : https://prove2.me/theorems/cce40c04-e4f0-4c34-b85d-7a5127de8ce7
-- title:
--   Continuous Blk M
-- statement:
--   Definitions and structural lemmas for Continuous Blk M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousBlkM.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_mem_hermC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
open scoped ComplexConjugate
def blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks b (Matrix.replicateCol (Fin 1) u) (Matrix.replicateRow (Fin 1) (star u))
      (Matrix.of fun _ _ => (d : ℂ)))
theorem blkM_mem {n : ℕ} (b : hermC n) (u : Fin n → ℂ) (d : ℝ) :
    blkM (b : Matrix (Fin n) (Fin n) ℂ) u d ∈ hermC (n + 1) := by
  have hb : (b : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b.2
  rw [mem_hermC]
  unfold blkM
  simp only [Matrix.reindex_apply]
  apply Matrix.IsHermitian.submatrix
  apply Matrix.IsHermitian.fromBlocks hb
  · ext i j
    simp [Matrix.conjTranspose_apply]
  · ext i j
    simp [Matrix.conjTranspose_apply]
def blk {n : ℕ} (b : hermC n) (u : Fin n → ℂ) (d : ℝ) : hermC (n + 1) :=
  ⟨blkM (b : Matrix (Fin n) (Fin n) ℂ) u d, blkM_mem b u d⟩
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt


