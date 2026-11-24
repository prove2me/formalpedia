-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerExtra
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerExtra
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:29.056421+00:00
-- url     : https://prove2.me/theorems/456a62b5-6cb0-481e-b4ed-8fa8b55610b3
-- title:
--   Imports Ter Extra
-- statement:
--   Definitions and structural lemmas for Imports Ter Extra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsTerExtra.lean

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
def regularityLocalDimension_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsLocalRing (locRing P W) ∧ IsNoetherianRing (locRing P W) ∧ ringKrullDim (locRing P W) = 1
end
end GroundTheory.Heights₂.Heights.Inter


