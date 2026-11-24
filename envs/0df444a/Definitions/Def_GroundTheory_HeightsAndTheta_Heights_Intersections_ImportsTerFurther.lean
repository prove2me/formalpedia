-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:29.538779+00:00
-- url     : https://prove2.me/theorems/584cc71e-823f-425b-8af4-4ef68052ae46
-- title:
--   Imports Ter Further
-- statement:
--   Definitions and structural lemmas for Imports Ter Further, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsTerFurther.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def RegularityFunctionFieldNumber.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∃ hF : IsField (funField P), @NumberField (funField P) hF.toField
end
end GroundTheory.Heights₂.Heights.Inter


