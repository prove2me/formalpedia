-- Prove2me | Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
-- name    : CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:41.941269+00:00
-- url     : https://prove2.me/theorems/a40b4a4a-6a9f-4df1-b357-6406c8ac3e55
-- title:
--   Metaplectic Unipotent Block Second Diag
-- statement:
--   Definitions and structural lemmas for Metaplectic Unipotent Block Second Diag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
namespace CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
def nn (S : Matrix l l ℝ) (t : ℝ) : Mat l := fromBlocks 1 (t • S) 0 1
def UU (S : Matrix l l ℝ) (t : ℝ) : Sch l →L[ℂ] Sch l :=
  fou l * (ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) * fouInv l)
end CompanionTheory.ThKR.Mp


