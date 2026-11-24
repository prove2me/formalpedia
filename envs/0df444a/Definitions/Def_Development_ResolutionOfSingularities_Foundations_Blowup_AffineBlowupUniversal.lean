-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversal
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversal
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:09:12.893254+00:00
-- url     : https://prove2.me/theorems/45832bcd-aa26-4941-8c34-0558f2df489e
-- title:
--   Affine Blowup Universal
-- statement:
--   Definitions and structural lemmas for Affine Blowup Universal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupUniversal.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.Blowup
universe u
def openCoverOfForallMem {W : Scheme.{u}} (U : ↥W → W.Opens) (hU : ∀ w, w ∈ U w) :
    W.OpenCover :=
  Scheme.Cover.mkOfCovers (↥W) (fun w => (U w).toScheme) (fun w => (U w).ι)
    (fun x => ⟨x, ⟨x, hU x⟩, rfl⟩)
end FunctorialResolution.Blowup


