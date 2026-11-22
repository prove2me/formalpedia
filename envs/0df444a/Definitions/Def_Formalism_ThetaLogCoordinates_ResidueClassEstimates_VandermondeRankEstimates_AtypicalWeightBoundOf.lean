-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
-- name    : Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:51.697688+00:00
-- url     : https://prove2.me/theorems/4548974e-be77-40e9-8edf-574361fc2347
-- title:
--   Atypical Weight Bound Of
-- statement:
--   Definitions and structural lemmas for Atypical Weight Bound Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean

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
namespace TTyp
end TTyp
namespace TTyp
end TTyp
namespace TTyp
def lat (q : ℕ → Bool) (B : ℕ → ℕ) (i : ℕ) : List ℕ := (((List.range' 1 i).filter q).reverse).map B
end TTyp
namespace TTyp
def revW (n : ℕ) (la : ℕ → ℤ) : ℕ → ℤ := fun m => -(la (n - 1 - m))
end TTyp
end Formalism.InvariantFactorPaths.BranchingDimensions


