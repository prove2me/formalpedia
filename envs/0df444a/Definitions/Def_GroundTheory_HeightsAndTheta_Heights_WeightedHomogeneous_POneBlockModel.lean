-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:22.5408+00:00
-- url     : https://prove2.me/theorems/e9c57de8-a515-46e6-adce-84dfbd975070
-- title:
--   POne Block Model
-- statement:
--   Definitions and structural lemmas for POne Block Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
namespace LatticeModel
variable {K : Type} [Field K] [NumberField K] {N r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)}
  {φ : Fin (N + 1) → Fin (r + 1) → K}
def genericT (K : Type) [Field K] (r : ℕ) : Fin r → LatticeField K r :=
  fun j ↦ algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (X j)
end LatticeModel
end
end GroundTheory.Heights₂.Heights


