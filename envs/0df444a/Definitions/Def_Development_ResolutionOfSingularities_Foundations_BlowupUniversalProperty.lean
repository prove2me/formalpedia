-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
-- name    : Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:54.505112+00:00
-- url     : https://prove2.me/theorems/d078a7fa-1ce7-47ea-a66b-600e9a8bb1da
-- title:
--   Blowup Universal Property
-- statement:
--   Definitions and structural lemmas for Blowup Universal Property, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/BlowupUniversalProperty.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.Blowup
def IsLocallyGeneratedByNonZeroDivisor {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U.1)),
    x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ I.ideal U = Ideal.span {f}
def IsBlowupAlongIdealSheaf {X X' : Scheme.{u}} (π : X' ⟶ X) (I : X.IdealSheafData) : Prop :=
  IsLocallyGeneratedByNonZeroDivisor (I.comap π) ∧
    ∀ (W : Scheme.{u}) (g : W ⟶ X), IsLocallyGeneratedByNonZeroDivisor (I.comap g) →
      ∃! h : W ⟶ X', h ≫ π = g
end FunctorialResolution.Blowup
end
end


