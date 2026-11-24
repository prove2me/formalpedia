-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_SmoothComponentsDisjoint
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_SmoothComponentsDisjoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:09.986806+00:00
-- url     : https://prove2.me/theorems/3e9cc6c8-ee1e-408d-91d9-a34bf58c4201
-- title:
--   Smooth Components Disjoint
-- statement:
--   Definitions and structural lemmas for Smooth Components Disjoint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/SmoothComponentsDisjoint.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_IrreducibleComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
def IrreducibleComponentsDisjointOfSmooth : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)),
    AlgebraicGeometry.Smooth p →
    ∀ C₁ ∈ irreducibleComponents ↥X, ∀ C₂ ∈ irreducibleComponents ↥X,
      C₁ ≠ C₂ → Disjoint C₁ C₂
end FunctorialResolution.EmbeddedResolution


