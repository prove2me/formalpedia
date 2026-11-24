-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:44.733988+00:00
-- url     : https://prove2.me/theorems/08c99598-6d04-4f09-9827-2da96c2f968f
-- title:
--   Blowup Properties
-- statement:
--   Definitions and structural lemmas for Blowup Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupProperties.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.Blowup
def StrictTransformIsBlowupOfClosedSubscheme : Prop :=
  ∀ (X X₁ S : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
    (j : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion j] (π : X₁ ⟶ X)
    (Z : X.IdealSheafData), IsBlowupAlongIdealSheaf π Z →
    (∀ T ∈ irreducibleComponents (↥S), ¬ (j.base '' T) ⊆ (Z.support : Set ↥X)) →
    ∃ ψ : (strictTransform π Z j.ker).subscheme ⟶ S,
      ψ ≫ j = (strictTransform π Z j.ker).subschemeι ≫ π ∧
        IsBlowupAlongIdealSheaf ψ (Z.comap j)
def BlowupIsProper : Prop :=
  ∀ (X X' : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X] (π : X' ⟶ X)
    (Z : X.IdealSheafData), IsBlowupAlongIdealSheaf π Z → AlgebraicGeometry.IsProper π
def BlowupIsIsoOffCenter : Prop :=
  ∀ (X X' : Scheme.{u}) (π : X' ⟶ X) (Z : X.IdealSheafData),
    IsBlowupAlongIdealSheaf π Z →
      CategoryTheory.IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl)
end FunctorialResolution.Blowup


