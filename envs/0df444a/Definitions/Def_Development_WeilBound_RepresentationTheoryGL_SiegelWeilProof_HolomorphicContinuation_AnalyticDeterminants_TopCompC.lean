-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompC
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:54.748299+00:00
-- url     : https://prove2.me/theorems/3f51fa83-12ab-4222-a0e9-4170b9b4792c
-- title:
--   Top Comp C
-- statement:
--   Definitions and structural lemmas for Top Comp C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TopCompC.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_StarExpNegI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def matrixBlockRestriction (s t : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a ∈ s ∧ b ∈ t then x a b else 0
def matrixBlockRestrictionLinear (s t : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := matrixBlockRestriction s t
      map_add' := fun x y => by ext a b; simp only [matrixBlockRestriction, Matrix.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by
        ext a b; simp only [matrixBlockRestriction, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp }
@[simp] theorem block_part_linear_apply (s t : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ) : matrixBlockRestrictionLinear s t x = matrixBlockRestriction s t x := rfl
def conjL (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => g * (Cm n * fromBlocks (P x) (Q x) (R x) (S x) * CmI n)
      map_add' := fun x y => by
        simp only [map_add, ← fromBlocks_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply, ← fromBlocks_smul, Matrix.mul_smul, Matrix.smul_mul] }
@[simp] theorem conjL_apply (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) : conjL g P Q R S x = g * (Cm n * fromBlocks (P x) (Q x) (R x) (S x) * CmI n) := rfl
def rotL (g : M2 n) (j : ℕ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => g * (rot j θ * fromBlocks 0 H 0 0 * (rot j θ)⁻¹)
      map_add' := fun x y => by
        rw [show fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (x + y) 0 0 = fromBlocks 0 x 0 0 + fromBlocks 0 y 0 0 by
          rw [fromBlocks_add]; simp]
        simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        rw [show fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • x) 0 0 = c • fromBlocks 0 x 0 0 by
          rw [fromBlocks_smul]; simp]
        simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
def topL (g : M2 n) (j : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  conjL g (((2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkA j) (blkB j)) (((2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkA j) (blkA j))
    ((-(2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkB j) (blkB j)) ((-(2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkB j) (blkA j))
end PositivityTheory.Rg.Sw.LVs.TC


