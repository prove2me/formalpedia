-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
-- name    : Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:28.073636+00:00
-- url     : https://prove2.me/theorems/b458439d-ffd9-464f-a26f-99ce61176dd6
-- title:
--   Branch
-- statement:
--   Definitions and structural lemmas for Branch, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
namespace Branch
def ff (j : ℕ) (x : ℝ) : ℝ := ∏ k ∈ range j, (x - k)
def W (n : ℕ) (u : ℕ → ℝ) : ℝ := ∏ j ∈ range n, ∏ i ∈ range j, (u j - u i)
end Branch
end Formalism.InvariantFactorPaths.BranchingDimensions


