-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
-- name    : Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:06.061819+00:00
-- url     : https://prove2.me/theorems/6e85d6b7-f2f5-46f9-b2ac-7582b02e31fb
-- title:
--   N0 Le Ns
-- statement:
--   Definitions and structural lemmas for N0 Le Ns, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean

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
open Letters
def revW (n : ℕ) (la : ℕ → ℤ) : ℕ → ℤ := fun m => -(la (n - 1 - m))
variable {D : Letters} {mu : D.Stages}
def actV (D : Letters) (l : ℕ) : Bool := decide (l ≤ D.n0) && D.vec l
def actC (D : Letters) (l : ℕ) : Bool := decide (l ≤ D.n0) && !D.vec l
end Formalism.InvariantFactorPaths.BranchingDimensions


