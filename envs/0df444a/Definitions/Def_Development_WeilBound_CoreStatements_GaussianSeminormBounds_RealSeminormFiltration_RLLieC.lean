-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieC
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieC
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:21:53.128579+00:00
-- url     : https://prove2.me/theorems/e5610c8b-5bc0-55dc-9f59-6344f8941356
-- title:
--   RLLie C
-- statement:
--   Definitions and structural lemmas for RLLie C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieC.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology
namespace PositivityTheory.RL.Up
section Banach
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
def expU (Z : 𝔸) : 𝔸ˣ :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  ⟨NormedSpace.exp Z, NormedSpace.exp (-Z),
    by rw [← NormedSpace.exp_add_of_commute (Commute.refl Z).neg_right, add_neg_cancel, NormedSpace.exp_zero],
    by rw [← NormedSpace.exp_add_of_commute (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero]⟩
end Banach
end PositivityTheory.RL.Up
end


