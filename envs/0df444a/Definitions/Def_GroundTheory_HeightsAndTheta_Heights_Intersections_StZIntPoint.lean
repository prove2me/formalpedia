-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StZIntPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StZIntPoint
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:52:56.621814+00:00
-- url     : https://prove2.me/theorems/fbfd217c-8851-55ba-a1c5-7c7addaa256c
-- title:
--   St ZInt Point
-- statement:
--   Definitions and structural lemmas for St ZInt Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StZIntPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CompsDim
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
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
def ZIntPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (φ : Fin 0 → MCone ι → ℝ),
    IsProjVar P 0 → Nonempty (Res ι P 0) → zInt P 0 φ (fun _ => 1) = 1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


