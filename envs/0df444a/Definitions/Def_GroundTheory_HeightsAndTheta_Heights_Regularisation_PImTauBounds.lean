-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:16.137259+00:00
-- url     : https://prove2.me/theorems/61004b11-18c7-48cf-b61a-587b6b1caa6e
-- title:
--   PIm Tau Bounds
-- statement:
--   Definitions and structural lemmas for PIm Tau Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Filter Topology
noncomputable section
def unitSphereDot (g : ℕ) : Set (Fin g → ℝ) := {u | u ⬝ᵥ u = 1}
namespace PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)
def realB (i : Fin a) : Matrix (Fin g) (Fin g) ℝ := (P.B i).map (Int.cast : ℤ → ℝ)
end PeriodPolydisc
end
end GroundTheory.Heights₂.Heights.Regular


