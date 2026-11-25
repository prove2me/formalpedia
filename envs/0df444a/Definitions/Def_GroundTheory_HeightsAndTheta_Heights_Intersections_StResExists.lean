-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StResExists
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StResExists
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:39:31.762413+00:00
-- url     : https://prove2.me/theorems/2142593f-5025-4089-beb4-5a57322729a8
-- title:
--   St Res Exists
-- statement:
--   Definitions and structural lemmas for St Res Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StResExists.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
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
def ResExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ), IsProjVar P e → Nonempty (Res ι P e)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


