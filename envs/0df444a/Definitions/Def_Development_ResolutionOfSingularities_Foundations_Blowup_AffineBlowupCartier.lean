-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:38:46.808499+00:00
-- url     : https://prove2.me/theorems/6e6abf58-6021-424d-933a-5dd32ddc9b03
-- title:
--   Affine Blowup Cartier
-- statement:
--   Definitions and structural lemmas for Affine Blowup Cartier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupCartier.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
def specIdealSheaf (I : Ideal R) : (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I)
def chartSectionsIso (I : Ideal R) (a : ↥I) :
    CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) ≅
      Γ(affineBlowup I, affineBlowupChart I a ''ᵁ ⊤) :=
  (Scheme.ΓSpecIso
      (CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).symm ≪≫
    ((affineBlowupChart I a).appIso ⊤).symm
end FunctorialResolution.Blowup


