-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_SmoothOrderOneCenters
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_SmoothOrderOneCenters
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:19.507932+00:00
-- url     : https://prove2.me/theorems/b389d56b-c178-4191-9653-499ccd9352f9
-- title:
--   Smooth Order One Centers
-- statement:
--   Definitions and structural lemmas for Smooth Order One Centers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/SmoothOrderOneCenters.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
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
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
structure PointedIrreducibleClosed (W : Scheme.{u}) where
  S : Set ↥W
  xi : ↥W
  pt : ↥W
  closedS : IsClosed S
  irredS : IsIrreducible S
  genericXi : IsGenericPoint xi S
  memPt : pt ∈ S
structure SmoothVanishingHypotheses (V : VanishingAssignment.{u}) : Prop where
  orderAt_vanishing_eq_one : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)), Smooth p →
      ∀ T : Closeds ↥W, IsIrreducible (T : Set ↥W) →
      Smooth ((V W T).subschemeι ≫ p) →
      (∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ (T : Set ↥W)) →
      ∀ x ∈ (T : Set ↥W), orderAt (V W T) x = 1
  smooth_opens_ι_comp : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens), Smooth p → Smooth (U.ι ≫ p)
  smooth_vanishing_hypersurface : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (H : (U.toScheme).IdealSheafData),
      IsSmoothDivisor (U.ι ≫ p) H →
      ∀ (T : Closeds ↥W) (S : Closeds ↥(H.subscheme)),
        (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W) →
        (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)) →
        Smooth ((V W T).subschemeι ≫ p) →
        Smooth ((V H.subscheme S).subschemeι ≫ (H.subschemeι ≫ (U.ι ≫ p)))
  smooth_vanishing_opens : ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (T : Closeds ↥W)
      (S : Closeds ↥(U.toScheme)),
      (S : Set ↥(U.toScheme)) = U.ι.base ⁻¹' (T : Set ↥W) →
      Smooth ((V W T).subschemeι ≫ p) →
      Smooth ((V U.toScheme S).subschemeι ≫ (U.ι ≫ p))
def SmoothOrderOneCentersIsolated (V : VanishingAssignment.{u}) {k : Type u} [Field k] [CharZero k]
    (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ)
    (Mem : Set ↥W) (Z : W.IdealSheafData) : Prop :=
  ∀ C : PointedIrreducibleClosed W, Smooth p → m = 1 →
    Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p) →
    (∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S) →
    C.xi ∉ (Z.support : Set ↥W) →
    Disjoint C.S Mem →
    (∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x) →
    C.pt ∈ (Z.support : Set ↥W) → False
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction


