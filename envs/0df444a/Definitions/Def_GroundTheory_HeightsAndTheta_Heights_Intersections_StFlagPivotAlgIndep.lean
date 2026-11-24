-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:09.278237+00:00
-- url     : https://prove2.me/theorems/e28c57c5-358d-4f6b-853b-fa9aedc83379
-- title:
--   St Flag Pivot Alg Indep
-- statement:
--   Definitions and structural lemmas for St Flag Pivot Alg Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StFlagPivotAlgIndep.lean

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
def FlagPivotAlgIndep.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ),
    AlgebraicIndependent F (fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => pivotMinor (genMat F n) q.1 q.2.1)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


