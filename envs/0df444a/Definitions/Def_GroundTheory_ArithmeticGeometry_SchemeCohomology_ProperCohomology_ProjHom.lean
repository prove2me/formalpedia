-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjHom
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjHom
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:15.723292+00:00
-- url     : https://prove2.me/theorems/ce023324-6a5d-521b-908f-9ff6d83adc71
-- title:
--   Proj Hom
-- statement:
--   Definitions and structural lemmas for Proj Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization
namespace GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
namespace ProjHom
variable {X : Scheme.{u}}
def toSpecAway (x : Γ(X, ⊤)) : (X.basicOpen x).toScheme ⟶ Spec (.of (Localization.Away x)) :=
  ((X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫ X.toSpecΓ ∣_ (PrimeSpectrum.basicOpen x)) ≫
    (basicOpenIsoSpecAway x).hom
def corr (g : X ⟶ Proj 𝒜) (r : A) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 r) :
    CommRingCat.of (Away 𝒜 r) ⟶ Γ(V, ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ (g.resLE _ V h ≫ Proj.basicOpenToSpec 𝒜 r).appTop
variable (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
end ProjHom
end
end GroundTheory.Arith.SchemeCoh


