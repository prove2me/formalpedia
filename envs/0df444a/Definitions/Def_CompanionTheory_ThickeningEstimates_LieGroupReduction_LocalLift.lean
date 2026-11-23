-- Prove2me | Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
-- name    : CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:53.900672+00:00
-- url     : https://prove2.me/theorems/771fa626-8aad-4ba7-9601-8481bc3b67b5
-- title:
--   Local Lift
-- statement:
--   Definitions and structural lemmas for Local Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
namespace CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
def bl (i j : l → l ⊕ l) : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] (Eu l →L[ℝ] Eu l) where
  toFun g := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (g.submatrix i j)
  map_add' g h := by rw [← map_add]; rfl
  map_smul' c g := by rw [RingHom.id_apply, ← map_smul]; rfl
end CompanionTheory.ThKR.LL
namespace CompanionTheory.ThKR
open LL
end CompanionTheory.ThKR


