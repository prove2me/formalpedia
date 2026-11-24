-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingInj
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingInj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:54.671862+00:00
-- url     : https://prove2.me/theorems/1f3e8756-b4a2-4438-acfc-6b7259cc957c
-- title:
--   St Loc Ring Inj
-- statement:
--   Definitions and structural lemmas for St Loc Ring Inj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StLocRingInj.lean

import Mathlib
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
def LocRingInj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W W' : Ideal (MRing ι)),
    P.IsPrime → IsMultiProjPrime W → IsMultiProjPrime W' → P ≤ W → P ≤ W' →
    locRing P W = locRing P W' → W = W'
end
end GroundTheory.Heights₂.Heights.Inter


