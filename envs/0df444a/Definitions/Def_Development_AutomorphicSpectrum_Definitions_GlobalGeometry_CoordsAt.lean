-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:15.408989+00:00
-- url     : https://prove2.me/theorems/43970dff-df3f-4c33-83e3-ac72c385d240
-- title:
--   Coords At
-- statement:
--   Definitions and structural lemmas for Coords At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/CoordsAt.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
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
def InChart (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type} (x : κ → Ω) (c : κ) (p : Cpt ξ) : Prop :=
  x c ≠ 0 ∧ ∀ c', x c' / x c ∈ regAt ξ p
structure CoordTie (o : Type) [CommRing o] [Algebra o Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type}
    (x : κ → Ω) : Prop where
  gen : IsCptGen ξ
  cover : ∀ p : Cpt ξ, ∃ c, InChart ξ x c p
  affine : ∀ c, x c ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧
    ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩
  ring : ∀ c, x c ≠ 0 → ∀ a : Ω, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔
    ∀ p : Cpt ξ, InChart ξ x c p → a ∈ regAt ξ p
variable {R : Type} [CommRing R] [IsLocalRing R]
def centre (z : Spec (CommRingCat.of R) ⟶ X) : X := z (IsLocalRing.closedPoint R)
def ValAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R) : Prop :=
  ∃ (h : genPt ξ ⤳ centre z) (s : X.presheaf.stalk (centre z)),
    genMap ξ ⟨centre z, h⟩ s = a ∧ (Scheme.stalkClosedPointTo z).hom s = r
def CoordsAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω)
    (z : Spec (CommRingCat.of R) ⟶ X) (w : (Σ k, ι k) → R) : Prop :=
  (∀ k, ∃ c, IsUnit (w ⟨k, c⟩)) ∧ ∀ k c, IsUnit (w ⟨k, c⟩) → y ⟨k, c⟩ ≠ 0 ∧
    ∀ i, ∃ r : R, ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c⟩) r ∧ w ⟨k, i⟩ = r * w ⟨k, c⟩
def InFibre (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : ℕ) (q : Cpt ξ) : Prop := ¬ unitAt ξ q (p : Ω)
end GlobalTheory.CompanionTheory.Ar


