-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementW
-- name    : Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:59.452315+00:00
-- url     : https://prove2.me/theorems/7b52d3c4-4fc3-464a-b1e9-94baefda157b
-- title:
--   Statement W
-- statement:
--   Definitions and structural lemmas for Statement W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/StatementW.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
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
namespace Formalism.InvariantFactorPaths.BranchingDimensions
def WeylGT : Prop :=
  BranchDim → ∀ (n : ℕ) (μ : Fin n → ℤ), Antitone μ → weylDim n (extW μ) = (Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT n μ : ℝ)
def PieriOfBranch : Prop := BranchDim → PieriDim
end Formalism.InvariantFactorPaths.BranchingDimensions


