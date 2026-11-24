-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:03.193815+00:00
-- url     : https://prove2.me/theorems/f54a630a-cea7-4550-9e23-66918e25e596
-- title:
--   Uniqueness Degree Form Of Intersection Form
-- statement:
--   Definitions and structural lemmas for Uniqueness Degree Form Of Intersection Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UniquenessDegreeFormOfIntersectionForm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
def ThmIUniquePosDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I J : Family ι),
    IsFamily I → IsFamily J → ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι),
      1 ≤ n → IsArithVar P n → AllSmooth L → I P n L = J P n L
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


