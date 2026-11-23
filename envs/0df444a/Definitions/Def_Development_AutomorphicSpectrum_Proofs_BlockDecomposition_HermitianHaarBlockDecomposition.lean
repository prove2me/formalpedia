-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianHaarBlockDecomposition
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianHaarBlockDecomposition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:41.4412+00:00
-- url     : https://prove2.me/theorems/ce14ac97-297c-48e0-97e7-e8856cc615f4
-- title:
--   Hermitian Haar Block Decomposition
-- statement:
--   Definitions and structural lemmas for Hermitian Haar Block Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianHaarBlockDecomposition.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
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
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
theorem blkM_castSucc_castSucc {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (i j : Fin n) : blkM b u d i.castSucc j.castSucc = b i j := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h]
theorem blkM_castSucc_last {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (i : Fin n) : blkM b u d i.castSucc (Fin.last n) = u i := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h, finSumFinEquiv_symm_last]
theorem blkM_last_last {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    blkM b u d (Fin.last n) (Fin.last n) = d := by
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]
theorem blkM_last_castSucc {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (j : Fin n) : blkM b u d (Fin.last n) j.castSucc = star (u j) := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h, finSumFinEquiv_symm_last]
theorem blkM_add {n : ℕ} (b b' : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ) (d d' : ℝ) :
    blkM (b + b') (u + u') (d + d') = blkM b u d + blkM b' u' d' := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [blkM_last_last]
    | cast j => simp [blkM_last_castSucc]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [blkM_castSucc_last]
    | cast j => simp [blkM_castSucc_castSucc]
def upperLeftHermBlock {n : ℕ} (b : hermC (n + 1)) : hermC n :=
  ⟨(b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix Fin.castSucc Fin.castSucc,
    mem_hermC.2 ((mem_hermC.1 b.2).submatrix _)⟩
def blkEquiv (n : ℕ) : (hermC n × (Fin n → ℂ) × ℝ) ≃+ hermC (n + 1) where
  toFun x := blk x.1 x.2.1 x.2.2
  invFun b := (upperLeftHermBlock b, fun i => (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i.castSucc (Fin.last n),
    ((b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n)).re)
  left_inv x := by
    obtain ⟨b, u, d⟩ := x
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
    · ext i j
      simp [upperLeftHermBlock, blk, blkM_castSucc_castSucc]
    · ext i
      simp [blk, blkM_castSucc_last]
    · simp [blk, blkM_last_last]
  right_inv b := by
    have hb := mem_hermC.1 b.2
    apply Subtype.ext
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp only [blk, blkM_last_last]
        have := hb.apply (Fin.last n) (Fin.last n)
        exact (Complex.conj_eq_iff_real.1 this).choose_spec ▸ by simp
      | cast j =>
        simp only [blk, blkM_last_castSucc]
        exact hb.apply _ _
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [blk, blkM_castSucc_last]
      | cast j => simp [blk, blkM_castSucc_castSucc, upperLeftHermBlock]
  map_add' x y := by
    apply Subtype.ext
    simp [blk, blkM_add]
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt


