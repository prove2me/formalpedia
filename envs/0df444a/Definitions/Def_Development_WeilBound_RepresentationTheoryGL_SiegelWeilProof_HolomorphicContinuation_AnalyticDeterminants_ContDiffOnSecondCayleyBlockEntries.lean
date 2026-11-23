-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:34.049323+00:00
-- url     : https://prove2.me/theorems/b24a9872-3d06-4c87-a908-9407bd54e086
-- title:
--   Cont Diff On Second Cayley Block Entries
-- statement:
--   Definitions and structural lemmas for Cont Diff On Second Cayley Block Entries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
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
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def Cinv (n : ℕ) : M2 n := ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks 1 (Complex.I • 1) (-1) (Complex.I • 1)
def mulLc (M : M2 n) : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ M)
theorem mulLc_apply (M v : M2 n) : mulLc M v = M * v := rfl
def mulLcL : M2 n →ₗ[ℂ] (M2 n →L[ℂ] M2 n) where
  toFun := mulLc
  map_add' a b := by ext1 v; simp [mulLc_apply, Matrix.add_mul]
  map_smul' c a := by ext1 v; simp [mulLc_apply, Matrix.smul_mul]
end PositivityTheory.Rg.Sw.LVs


