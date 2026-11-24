-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerLast
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerLast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:29.249045+00:00
-- url     : https://prove2.me/theorems/d81b7fe4-702f-4114-b707-1cb17ec2430e
-- title:
--   Imports Ter Last
-- statement:
--   Definitions and structural lemmas for Imports Ter Last, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsTerLast.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemRegRingSpecZ
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
def RegularityIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ x : regRing P, IsIntegral ℤ ((x : funField P) : FractionRing (MRing ι ⧸ P))
end
end GroundTheory.Heights₂.Heights.Inter


