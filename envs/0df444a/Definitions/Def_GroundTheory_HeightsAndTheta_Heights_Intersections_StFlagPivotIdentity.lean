-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:17.860606+00:00
-- url     : https://prove2.me/theorems/218bd165-70ef-48f4-b255-da22831c7d8d
-- title:
--   St Flag Pivot Identity
-- statement:
--   Definitions and structural lemmas for St Flag Pivot Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StFlagPivotIdentity.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagPivot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
def FlagPivotIdentity.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (S : PluckerBlocks n n j),
    flagMinor M j S * ∏ a ∈ Finset.Iic j, leadMinor M a = leadMinor M j * flagMinor (pivotMatrix M) j S
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


