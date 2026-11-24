-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:33.69204+00:00
-- url     : https://prove2.me/theorems/56929240-c7d7-41e4-b946-1bc7080163c2
-- title:
--   Blowup Open Cover
-- statement:
--   Definitions and structural lemmas for Blowup Open Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupOpenCover.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
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
universe u v
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
namespace FunctorialResolution.Blowup
theorem exists_pullback_fst_base_eq {W U X : Scheme.{u}} (g : W ⟶ X) (f : U ⟶ X)
    [IsOpenImmersion f] (w : W) (hw : g.base w ∈ Set.range ⇑f.base) :
    ∃ z : ↥(pullback g f), (pullback.fst g f).base z = w := by
  have hrange : Set.range ⇑((g ⁻¹ᵁ f.opensRange).ι ≫ g).base ⊆ Set.range ⇑f.base := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  have hl : IsOpenImmersion.lift f ((g ⁻¹ᵁ f.opensRange).ι ≫ g) hrange ≫ f
      = (g ⁻¹ᵁ f.opensRange).ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hm := pullback.lift_fst (g ⁻¹ᵁ f.opensRange).ι
    (IsOpenImmersion.lift f ((g ⁻¹ᵁ f.opensRange).ι ≫ g) hrange) hl.symm
  refine ⟨(pullback.lift (g ⁻¹ᵁ f.opensRange).ι
    (IsOpenImmersion.lift f ((g ⁻¹ᵁ f.opensRange).ι ≫ g) hrange) hl.symm).base
      ⟨w, show w ∈ g ⁻¹ᵁ f.opensRange from hw⟩, ?_⟩
  have h3 := congrArg (fun t : (g ⁻¹ᵁ f.opensRange).toScheme ⟶ W => t.base
    ⟨w, show w ∈ g ⁻¹ᵁ f.opensRange from hw⟩) hm
  exact h3
noncomputable def pullbackOpenCoverOfCovers {X W : Scheme.{u}} {ι : Type v} (U : ι → Scheme.{u})
    (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base) (g : W ⟶ X) : W.OpenCover :=
  Scheme.Cover.mkOfCovers ι (fun i => pullback g (f i)) (fun i => pullback.fst g (f i))
    (fun w => by
      obtain ⟨i, hi⟩ := hcover (g.base w)
      obtain ⟨z, hz⟩ := exists_pullback_fst_base_eq g (f i) w hi
      exact ⟨i, z, hz⟩)
    (fun i => inferInstance)
end FunctorialResolution.Blowup


