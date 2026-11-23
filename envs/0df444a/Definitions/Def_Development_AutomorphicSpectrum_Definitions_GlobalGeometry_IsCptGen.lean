-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:51.52767+00:00
-- url     : https://prove2.me/theorems/efe129b1-7331-4f9f-a4a8-c2955f0f7e6b
-- title:
--   Is Cpt Gen
-- statement:
--   Definitions and structural lemmas for Is Cpt Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsCptGen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
def genPt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : X := ξ (IsLocalRing.closedPoint Ω)
def Cpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Type := {p : X // genPt ξ ⤳ p}
def genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : X.presheaf.stalk p.1 →+* Ω :=
  (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom
def regAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Subring Ω := (genMap ξ p).range
def unitAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) : Prop :=
  a ≠ 0 ∧ a ∈ regAt ξ p ∧ a⁻¹ ∈ regAt ξ p
structure IsCptGen (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Prop where
  bij : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom
  inj : ∀ p : Cpt ξ, Function.Injective (genMap ξ p)
end GlobalTheory.CompanionTheory.Ar


