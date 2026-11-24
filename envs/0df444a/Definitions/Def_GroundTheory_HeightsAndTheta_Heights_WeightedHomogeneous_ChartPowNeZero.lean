-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartPowNeZero
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartPowNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:18.563374+00:00
-- url     : https://prove2.me/theorems/c0fcb5e4-c28a-44da-88b9-5b64329459ff
-- title:
--   Chart Pow Ne Zero
-- statement:
--   Definitions and structural lemmas for Chart Pow Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartPowNeZero.lean

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
open MvPolynomial
noncomputable section
namespace AddBlockData
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
end AddBlockData
end
end GroundTheory.Heights₂.Heights


