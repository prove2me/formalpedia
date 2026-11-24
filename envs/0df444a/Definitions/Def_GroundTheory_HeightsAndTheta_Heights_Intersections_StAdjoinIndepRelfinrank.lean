-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StAdjoinIndepRelfinrank
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StAdjoinIndepRelfinrank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:58.347788+00:00
-- url     : https://prove2.me/theorems/102b6033-765a-4a06-8ded-67f9fac48098
-- title:
--   St Adjoin Indep Relfinrank
-- statement:
--   Definitions and structural lemmas for St Adjoin Indep Relfinrank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StAdjoinIndepRelfinrank.lean

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
def AdjoinIndepRelfinrank.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (L₀ L : IntermediateField F Ω) (ι : Type) (t : ι → Ω),
    L₀ ≤ L → AlgebraicIndependent L t →
      IntermediateField.relfinrank (L₀ ⊔ IntermediateField.adjoin F (Set.range t))
          (L ⊔ IntermediateField.adjoin F (Set.range t)) =
        IntermediateField.relfinrank L₀ L
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


