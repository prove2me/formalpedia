-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_CertificateOpenRestriction
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_CertificateOpenRestriction
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:54:00.687524+00:00
-- url     : https://prove2.me/theorems/0d953762-f608-47c5-a2d5-2e39d816adc8
-- title:
--   Certificate Open Restriction
-- statement:
--   Definitions and structural lemmas for Certificate Open Restriction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/CertificateOpenRestriction.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
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
namespace FunctorialResolution.EmbeddedResolution
noncomputable def comapSubscheme {V W : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData) :
    (D.comap f).subscheme ⟶ D.subscheme :=
  Scheme.IdealSheafData.subschemeMap (D.comap f) D f (D.le_map_comap f)
structure OpenImmersionStability (k : Type u) [Field k] : Prop where
  comap_nonzeroOnComponents :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (J : W.IdealSheafData),
      NonzeroOnComponents J → NonzeroOnComponents (J.comap f)
  isOpenImmersion_comapSubscheme :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (D : W.IdealSheafData),
      IsOpenImmersion (comapSubscheme f D)
  comap_isSmoothDivisor :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f]
      (p : W ⟶ Spec (CommRingCat.of k)) (D : W.IdealSheafData),
      IsSmoothDivisor p D → IsSmoothDivisor (f ≫ p) (D.comap f)
def IsPrincipalizationCertificateOnOpens {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  ∀ (V : Scheme.{u}) (f : V ⟶ W), IsOpenImmersion f →
    PrincipalizationCertificate V (f ≫ p) (I.comap f) m (⇑f.base ⁻¹' Mem) (Z.comap f)
def IsOrderCertificateOnOpens {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  ∀ (V : Scheme.{u}) (f : V ⟶ W), IsOpenImmersion f →
    OrderCertificate V (f ≫ p) (N.comap f) μ (⇑f.base ⁻¹' Mem) (Z.comap f)
end FunctorialResolution.EmbeddedResolution


