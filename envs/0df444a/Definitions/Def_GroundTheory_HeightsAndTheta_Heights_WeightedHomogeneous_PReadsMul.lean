-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PReadsMul
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PReadsMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:26:22.011646+00:00
-- url     : https://prove2.me/theorems/63b0e668-beb5-483a-850b-f3979671128c
-- title:
--   PReads Mul
-- statement:
--   Definitions and structural lemmas for PReads Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PReadsMul.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
namespace ReadsMul
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
end ReadsMul
end
end GroundTheory.Heights₂.Heights


