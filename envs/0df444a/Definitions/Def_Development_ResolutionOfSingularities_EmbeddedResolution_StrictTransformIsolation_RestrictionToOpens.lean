-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:19.480853+00:00
-- url     : https://prove2.me/theorems/a0933f84-8ced-4933-9a4c-983a2be6f68b
-- title:
--   Restriction To Opens
-- statement:
--   Definitions and structural lemmas for Restriction To Opens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/RestrictionToOpens.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
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
abbrev VanishingAssignment := ∀ X : Scheme.{u}, Closeds ↥X → X.IdealSheafData
structure IrreducibleClosedPair (W : Scheme.{u}) where
  S1 : Set ↥W
  S2 : Set ↥W
  xi1 : ↥W
  xi2 : ↥W
  pt : ↥W
  closed1 : IsClosed S1
  closed2 : IsClosed S2
  irred1 : IsIrreducible S1
  irred2 : IsIrreducible S2
  generic1 : IsGenericPoint xi1 S1
  generic2 : IsGenericPoint xi2 S2
  mem_first_closed : pt ∈ S1
  mem_second_closed : pt ∈ S2
def AgreeNear {W : Scheme.{u}} (I J : W.IdealSheafData) (x : ↥W) : Prop :=
  ∃ U : W.Opens, x ∈ U ∧ I.comap U.ι = J.comap U.ι
structure IdealSheafGeometryHypotheses (V : VanishingAssignment.{u}) : Prop where
  agreeNear_comap : ∀ (W : Scheme.{u}) (U : W.Opens) (I J : W.IdealSheafData)
      (y : ↥(U.toScheme)), AgreeNear I J (U.ι.base y) →
      AgreeNear (I.comap U.ι) (J.comap U.ι) y
  agreeNear_trans : ∀ (W : Scheme.{u}) (I J K : W.IdealSheafData) (x : ↥W),
      AgreeNear I J x → AgreeNear J K x → AgreeNear I K x
  comap_mul : ∀ (W X : Scheme.{u}) (f : X ⟶ W) (I J : W.IdealSheafData),
      (I * J).comap f = I.comap f * J.comap f
  base_comp : ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X),
      (f ≫ g).base x = g.base (f.base x)
  isClosed_support : ∀ (W : Scheme.{u}) (I : W.IdealSheafData),
      IsClosed (I.support : Set ↥W)
  isClosedEmbedding_subschemeι : ∀ (W : Scheme.{u}) (I : W.IdealSheafData),
      Topology.IsClosedEmbedding ⇑I.subschemeι.base
  isEmbedding_ι : ∀ (W : Scheme.{u}) (U : W.Opens), Topology.IsEmbedding ⇑U.ι.base
  isOpen_opens : ∀ (W : Scheme.{u}) (U : W.Opens), IsOpen (U : Set ↥W)
  orderAt_comap : ∀ (W : Scheme.{u}) (U : W.Opens) (I : W.IdealSheafData)
      (y : ↥(U.toScheme)), orderAt (I.comap U.ι) y = orderAt I (U.ι.base y)
  orderAt_congr : ∀ (W : Scheme.{u}) (I J : W.IdealSheafData) (x : ↥W),
      AgreeNear I J x → orderAt I x = orderAt J x
  orderAt_vanishing_eq_one : ∀ (k : Type u) [Field k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (D : (U.toScheme).IdealSheafData),
      IsSmoothDivisor (U.ι ≫ p) D →
      ∀ (T : Closeds ↥(D.subscheme)) (y : ↥(D.subscheme)),
        IsGenericPoint y (T : Set ↥(D.subscheme)) →
        (T : Set ↥(D.subscheme)) ∉ irreducibleComponents ↥(D.subscheme) →
        orderAt (V D.subscheme T) y = 1
  range_ι : ∀ (W : Scheme.{u}) (U : W.Opens), Set.range ⇑U.ι.base = (U : Set ↥W)
  range_subschemeι : ∀ (W : Scheme.{u}) (I : W.IdealSheafData),
      Set.range ⇑I.subschemeι.base = (I.support : Set ↥W)
  support_mul : ∀ (W : Scheme.{u}) (I J : W.IdealSheafData),
      ((I * J).support : Set ↥W) = (I.support : Set ↥W) ∪ (J.support : Set ↥W)
  not_subset_support_of_nonzeroOnComponents : ∀ (W : Scheme.{u}) (I : W.IdealSheafData),
      NonzeroOnComponents I →
      ∀ T ∈ irreducibleComponents ↥W, ¬ T ⊆ (I.support : Set ↥W)
  support_vanishing : ∀ (W : Scheme.{u}) (T : Closeds ↥W),
      ((V W T).support : Set ↥W) = (T : Set ↥W)
  top_mul : ∀ (W : Scheme.{u}) (I : W.IdealSheafData), (⊤ : W.IdealSheafData) * I = I
  agreeNear_vanishing_restrict : ∀ (W : Scheme.{u}) (I : W.IdealSheafData) (U : W.Opens)
      (D : (U.toScheme).IdealSheafData) (T : Closeds ↥W) (T' : Closeds ↥(D.subscheme))
      (y : ↥(D.subscheme)),
      (T' : Set ↥(D.subscheme)) = (D.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W) →
      (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (D.support : Set ↥(U.toScheme)) →
      AgreeNear I (V W T) ((D.subschemeι ≫ U.ι).base y) →
      AgreeNear ((I.comap U.ι).comap D.subschemeι) (V D.subscheme T') y
  comap_vanishing : ∀ (W : Scheme.{u}) (T : Closeds ↥W) (U : W.Opens)
      (T' : Closeds ↥(U.toScheme)),
      (T' : Set ↥(U.toScheme)) = U.ι.base ⁻¹' (T : Set ↥W) →
      (V W T).comap U.ι = V U.toScheme T'
def OrderOneCentersIsolated (V : VanishingAssignment.{u}) {k : Type u} [Field k] (W : Scheme.{u})
    (_p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  ∀ C : IrreducibleClosedPair W, m = 1 → C.S1 ⊆ (Z.support : Set ↥W) →
    C.xi2 ∉ (Z.support : Set ↥W) → C.xi1 ∉ Mem → C.xi2 ∉ Mem →
    AgreeNear I (V W ⟨C.S1, C.closed1⟩) C.xi1 → orderAt I C.xi1 = 1 →
    C.xi2 ∈ (I.support : Set ↥W) → False
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction


