-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRelAlgClosureFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StRelAlgClosureFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:29:13.052374+00:00
-- url     : https://prove2.me/theorems/b92aa31f-3b33-4068-bc8a-982da57756b8
-- title:
--   St Rel Alg Closure Finite
-- statement:
--   Definitions and structural lemmas for St Rel Alg Closure Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StRelAlgClosureFinite.lean

import Mathlib
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
namespace GroundTheory.Heights₂.Heights.Inter
def RelAlgClosureFinite.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (S : Finset L),
    IntermediateField.adjoin K (S : Set L) = ⊤ → FiniteDimensional K (algebraicClosure K L)
end GroundTheory.Heights₂.Heights.Inter


