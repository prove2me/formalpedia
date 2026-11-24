-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_DerivationLiftAndDeterminant
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_DerivationLiftAndDeterminant
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:10:32.074794+00:00
-- url     : https://prove2.me/theorems/ddb0d26d-0f20-4bb6-91d8-dea28dd9139d
-- title:
--   Derivation Lift And Determinant
-- statement:
--   Definitions and structural lemmas for Derivation Lift And Determinant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/DerivationLiftAndDeterminant.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
end
section
variable {R : Type*} [CommRing R]
end
section
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
theorem derivation_mapsTo_span_self {B : Type*} [CommRing B] [Algebra k B]
    (D : Derivation k B B) (h : B) (hD : D h = 0) :
    ∀ x ∈ Ideal.span ({h} : Set B), D x ∈ Ideal.span ({h} : Set B) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Derivation.leibniz, hD, smul_zero, zero_add, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self h)
theorem algHom_map_derivation_eq_zero (π : R →ₐ[k] S) (h : R)
    (hker : RingHom.ker π.toRingHom = Ideal.span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) :
    ∀ r : R, π r = 0 → π (D r) = 0 := by
  intro r hr
  have hrk : r ∈ Ideal.span ({h} : Set R) := by
    rw [← hker]
    exact hr
  have h2 : D r ∈ Ideal.span ({h} : Set R) := derivation_mapsTo_span_self D h hD r hrk
  rw [← hker] at h2
  have h3 : π.toRingHom (D r) = 0 := RingHom.mem_ker.mp h2
  exact h3
def liftDerivationOfKerEqSpan (π : R →ₐ[k] S) (hπ : Function.Surjective π) (h : R)
    (hker : RingHom.ker π.toRingHom = Ideal.span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) : Derivation k S S :=
  D.liftOfSurjective hπ (algHom_map_derivation_eq_zero π h hker D hD)
end
section
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
end
section
variable {X : Scheme.{u}} {k : Type u} [Field k]
end
end FunctorialResolution.EmbeddedResolution


