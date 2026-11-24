-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTer
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:58.245063+00:00
-- url     : https://prove2.me/theorems/db1ba041-68df-4949-bb16-5f9f84b5922c
-- title:
--   Imports More Ter
-- statement:
--   Definitions and structural lemmas for Imports More Ter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsMoreTer.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemRegRingSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLeRingKrullDim
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
def RegularityLocalize.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsClosedPt W → P ≤ W → y ∈ locRing P W →
    ∃ s x : regRing P, (∃ z ∈ locRing P W, ((s : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1) ∧
      y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))
end
end GroundTheory.Heights₂.Heights.Inter


