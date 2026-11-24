-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFinrankAdjoinRange
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StFinrankAdjoinRange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:58.92916+00:00
-- url     : https://prove2.me/theorems/8a3576dd-a7d5-4da3-ad16-a6d1a59a1515
-- title:
--   St Finrank Adjoin Range
-- statement:
--   Definitions and structural lemmas for St Finrank Adjoin Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StFinrankAdjoinRange.lean

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
def FinrankAdjoinRange.Statement : Prop :=
  ∀ (F Φ Ω : Type) [Field F] [Field Φ] [Field Ω] [Algebra F Φ] [Algebra F Ω] [Algebra Φ Ω] [IsScalarTower F Φ Ω]
    (S : Set Ω),
    Module.finrank Φ (IntermediateField.adjoin Φ S) =
      IntermediateField.relfinrank (IsScalarTower.toAlgHom F Φ Ω).fieldRange
        ((IsScalarTower.toAlgHom F Φ Ω).fieldRange ⊔ IntermediateField.adjoin F S)
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


