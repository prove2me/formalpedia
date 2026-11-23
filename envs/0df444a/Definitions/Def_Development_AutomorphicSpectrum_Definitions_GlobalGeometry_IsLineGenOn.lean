-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsLineGenOn
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsLineGenOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:57.606139+00:00
-- url     : https://prove2.me/theorems/8e5df90a-20e6-42a5-a1f1-ee3fb9b42d9a
-- title:
--   Is Line Gen On
-- statement:
--   Definitions and structural lemmas for Is Line Gen On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsLineGenOn.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}
def IsCoeffAt (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (x : Cpt ξ) (f : Ω) : Prop :=
  ∃ α β : Ω, α ≠ 0 ∧ β ≠ 0 ∧ A.wedge p x = Submodule.span (regAt ξ x) {α • a} ∧
    B.wedge q x = Submodule.span (regAt ξ x) {β • b} ∧ f * α = β
def IsLineGenOn (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (T : Set (Cpt ξ)) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ ∀ x ∈ T, IsCoeffAt A B p q a b x 1
end GlobalTheory.CompanionTheory.Ar.Flat


