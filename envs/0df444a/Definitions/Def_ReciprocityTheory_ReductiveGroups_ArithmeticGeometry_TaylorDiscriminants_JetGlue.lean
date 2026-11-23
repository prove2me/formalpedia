-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JetGlue
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JetGlue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:56.288812+00:00
-- url     : https://prove2.me/theorems/2db57d9c-bcbb-48f3-a422-106eecc31e9c
-- title:
--   Jet Glue
-- statement:
--   Definitions and structural lemmas for Jet Glue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/JetGlue.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace ReciprocityTheory.ChartRestriction.G.TB
abbrev JetRing (S : Type) [CommRing S] (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ S ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ S))) ^ (m + 1)
abbrev JetLoc (S : Type) [CommRing S] (κ : Type) (m : ℕ) (𝔭 : Ideal S) [𝔭.IsPrime] : Type :=
  Localization (Algebra.algebraMapSubmonoid (JetRing S κ m) 𝔭.primeCompl)
def JetGlueSt : Prop :=
  ∀ (S : Type) [CommRing S] (κ : Type) [Finite κ] (m : ℕ) (X : Scheme.{0})
    (f g : Spec (CommRingCat.of (JetRing S κ m)) ⟶ X),
    (∀ (𝔭 : Ideal S) [𝔭.IsPrime],
      Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) ≫ g) →
    f = g
end ReciprocityTheory.ChartRestriction.G.TB


