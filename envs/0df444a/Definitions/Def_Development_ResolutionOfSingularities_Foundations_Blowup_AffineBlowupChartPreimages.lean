-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:53:49.86999+00:00
-- url     : https://prove2.me/theorems/049caa63-16b4-42a2-9610-bd252951aef6
-- title:
--   Affine Blowup Chart Preimages
-- statement:
--   Definitions and structural lemmas for Affine Blowup Chart Preimages, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
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
def sectionsRingHom {A : Type u} [CommRing A] {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of A)) (V : W.Opens) : A →+* ↥Γ(W, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    g.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top g).ge)).hom
def chartSectionsRingHom {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (h : W ⟶ affineBlowup I) (b : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I b ''ᵁ ⊤)) :
    HomogeneousLocalization.Away (reesGrading I) (reesGenerator I b) →+* ↥Γ(W, V) :=
  ((chartSectionsIso I b).hom ≫ h.appLE (affineBlowupChart I b ''ᵁ ⊤) V hV).hom
def openCoverBySpecOfIsAffineOpen {W : Scheme.{u}} (VV : ↥W → W.Opens)
    (hVaff : ∀ w : ↥W, IsAffineOpen (VV w)) (hmem : ∀ w : ↥W, w ∈ VV w) : W.OpenCover :=
  Scheme.Cover.mkOfCovers ↥W (fun w => Spec Γ(W, VV w)) (fun w => (hVaff w).fromSpec)
    (fun x => by
      have hx : x ∈ Set.range ((hVaff x).fromSpec).base := by
        rw [(hVaff x).range_fromSpec]
        exact hmem x
      obtain ⟨y, hy⟩ := hx
      exact ⟨x, y, hy⟩)
    (fun w => inferInstance)
end FunctorialResolution.Blowup


