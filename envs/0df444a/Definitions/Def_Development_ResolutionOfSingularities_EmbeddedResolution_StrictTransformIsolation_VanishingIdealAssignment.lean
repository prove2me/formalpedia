-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:00.566849+00:00
-- url     : https://prove2.me/theorems/f0a5d94c-5103-4b74-8d6f-fd7d7ab7df81
-- title:
--   Vanishing Ideal Assignment
-- statement:
--   Definitions and structural lemmas for Vanishing Ideal Assignment, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealAssignment.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
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
noncomputable def vanishingIdealAssignment : VanishingAssignment.{u} :=
  fun _ T => Scheme.IdealSheafData.vanishingIdeal T
def VanishingOrderOneOnSmoothDivisor : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (U : W.Opens) (D : (U.toScheme).IdealSheafData),
    IsSmoothDivisor (U.ι ≫ p) D →
    ∀ (T : Closeds ↥(D.subscheme)) (y : ↥(D.subscheme)),
      IsGenericPoint y (T : Set ↥(D.subscheme)) →
      (T : Set ↥(D.subscheme)) ∉ irreducibleComponents ↥(D.subscheme) →
      orderAt (vanishingIdealAssignment D.subscheme T) y = 1
def AgreeNearVanishingComapSubscheme : Prop :=
  ∀ (W : Scheme.{u}) (N : W.IdealSheafData) (U : W.Opens)
    (H : (U.toScheme).IdealSheafData) (T : Closeds ↥W) (S : Closeds ↥(H.subscheme))
    (x : ↥(H.subscheme)),
    (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W) →
    (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)) →
    AgreeNear N (vanishingIdealAssignment W T) ((H.subschemeι ≫ U.ι).base x) →
    AgreeNear ((N.comap U.ι).comap H.subschemeι) (vanishingIdealAssignment H.subscheme S) x
def VanishingComapOpens : Prop :=
  ∀ (W : Scheme.{u}) (T : Closeds ↥W) (V : W.Opens) (S : Closeds ↥(V.toScheme)),
    (S : Set ↥(V.toScheme)) = V.ι.base ⁻¹' (T : Set ↥W) →
    (vanishingIdealAssignment W T).comap V.ι = vanishingIdealAssignment V.toScheme S
def OrderAtEqOfAgreeNear : Prop :=
  ∀ (W : Scheme.{u}) (I J : W.IdealSheafData) (x : ↥W),
    AgreeNear I J x → orderAt I x = orderAt J x
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction


