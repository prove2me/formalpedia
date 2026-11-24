-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingNoeth
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingNoeth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:23.860099+00:00
-- url     : https://prove2.me/theorems/24c71124-356e-4b5a-8008-397cf583d1f3
-- title:
--   St Loc Ring Noeth
-- statement:
--   Definitions and structural lemmas for St Loc Ring Noeth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StLocRingNoeth.lean

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
def LocRingNoeth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W → IsRelevant W → IsNoetherianRing (locRing P W)
end
end GroundTheory.Heights₂.Heights.Inter


