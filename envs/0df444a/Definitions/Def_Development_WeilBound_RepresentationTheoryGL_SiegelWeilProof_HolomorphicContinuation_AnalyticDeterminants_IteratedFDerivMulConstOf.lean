-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:17.773747+00:00
-- url     : https://prove2.me/theorems/3e69610f-7c53-41ea-8614-27609b2f8c16
-- title:
--   Iterated FDeriv Mul Const Of
-- statement:
--   Definitions and structural lemmas for Iterated FDeriv Mul Const Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
theorem embOn_add (s : Finset (Fin n)) (T T' : Matrix s s ℂ) : embOn s (T + T') = embOn s T + embOn s T' := by
  ext a b; simp only [embOn, Matrix.add_apply]; split_ifs <;> simp
theorem embOn_smul (s : Finset (Fin n)) (c : ℂ) (T : Matrix s s ℂ) : embOn s (c • T) = c • embOn s T := by
  ext a b; simp only [embOn, Matrix.smul_apply]; split_ifs <;> simp
theorem WD_add (Q Q' R R' : Matrix (Fin n) (Fin n) ℂ) : WD (Q + Q') (R + R') = WD Q R + WD Q' R' := by
  have : fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (Q + Q') (R + R') 0 = fromBlocks 0 Q R 0 + fromBlocks 0 Q' R' 0 := by
    rw [Matrix.fromBlocks_add, add_zero]
  simp only [WD, this, Matrix.mul_add, Matrix.add_mul]
theorem WD_smul (c : ℂ) (Q R : Matrix (Fin n) (Fin n) ℂ) : WD (c • Q) (c • R) = c • WD Q R := by
  have : fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • Q) (c • R) 0 = c • fromBlocks 0 Q R 0 := by
    rw [Matrix.fromBlocks_smul, smul_zero]
  simp only [WD, this, Matrix.mul_smul, Matrix.smul_mul]
def LQ (s : Finset (Fin n)) (x : M2 n) : Matrix s s ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => x * WD (embOn s T) 0
      map_add' := fun T T' => by
        have h := WD_add (embOn s T) (embOn s T') (0 : Matrix (Fin n) (Fin n) ℂ) 0
        rw [add_zero] at h
        rw [embOn_add, h, Matrix.mul_add]
      map_smul' := fun c T => by
        have h := WD_smul c (embOn s T) (0 : Matrix (Fin n) (Fin n) ℂ)
        rw [smul_zero] at h
        simp only [RingHom.id_apply]
        rw [embOn_smul, h, Matrix.mul_smul] }
def LR (s : Finset (Fin n)) (x : M2 n) : Matrix s s ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => x * WD 0 (embOn s T)
      map_add' := fun T T' => by
        have h := WD_add (0 : Matrix (Fin n) (Fin n) ℂ) 0 (embOn s T) (embOn s T')
        rw [add_zero] at h
        rw [embOn_add, h, Matrix.mul_add]
      map_smul' := fun c T => by
        have h := WD_smul c (0 : Matrix (Fin n) (Fin n) ℂ) (embOn s T)
        rw [smul_zero] at h
        simp only [RingHom.id_apply]
        rw [embOn_smul, h, Matrix.mul_smul] }
end PositivityTheory.Rg.Sw.LVs


