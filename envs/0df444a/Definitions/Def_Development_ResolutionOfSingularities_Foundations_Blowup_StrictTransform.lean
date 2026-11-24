-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:45.290795+00:00
-- url     : https://prove2.me/theorems/952210b1-ab08-429b-84a4-8e2b0ec80652
-- title:
--   Strict Transform
-- statement:
--   Definitions and structural lemmas for Strict Transform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace FunctorialResolution.Blowup
noncomputable section
def exceptionalIdeal {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    X'.IdealSheafData :=
  Z.comap f
def strictTransformOpens {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    ((J.comap f).subscheme).Opens :=
  (J.comap f).subschemeι ⁻¹ᵁ (Z.comap f).support.compl
def strictTransformImmersion {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    (strictTransformOpens f Z J).toScheme ⟶ X' :=
  (strictTransformOpens f Z J).ι ≫ (J.comap f).subschemeι
def strictTransform {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    X'.IdealSheafData :=
  (strictTransformImmersion f Z J).ker
def schemeImageIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) : Y.IdealSheafData :=
  (I.subschemeι ≫ f).ker
end
end FunctorialResolution.Blowup


