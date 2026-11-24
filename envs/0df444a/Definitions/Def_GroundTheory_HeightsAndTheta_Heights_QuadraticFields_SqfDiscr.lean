-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_QuadraticFields_SqfDiscr
-- name    : GroundTheory_HeightsAndTheta_Heights_QuadraticFields_SqfDiscr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:34.434743+00:00
-- url     : https://prove2.me/theorems/01f2e5e2-7d95-4cdb-9223-39151f2b49a6
-- title:
--   Sqf Discr
-- statement:
--   Definitions and structural lemmas for Sqf Discr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/QuadraticFields/SqfDiscr.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_QuadraticFields_SqfField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Rows
def SqfDiscr.Statement : Prop :=
  ∀ d : ℕ, Squarefree d → d % 4 = 3 →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      ∀ x : K, x ^ 2 = -(d : K) → NumberField.discr K = -(d : ℤ)
end GroundTheory.Heights₂.Heights.Rows


