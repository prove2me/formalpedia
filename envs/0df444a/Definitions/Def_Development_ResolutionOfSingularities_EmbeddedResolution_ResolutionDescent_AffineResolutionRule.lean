-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:23.356813+00:00
-- url     : https://prove2.me/theorems/6b2bac85-30c1-4640-9d17-a1f85176aaeb
-- title:
--   Affine Resolution Rule
-- statement:
--   Definitions and structural lemmas for Affine Resolution Rule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineResolutionRule.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def AffineEmbedsIntoAffineSpace : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p],
    ∃ (n : ℕ) (e : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))),
      AlgebraicGeometry.IsClosedImmersion e ∧ NonzeroOnComponents e.ker ∧
        e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) = p
def NilIsStrictNormalCrossingsOnAffineSpace : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u} (Fin n))).IdealSheafData)
def AffineSpaceIsSmooth : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
def ClosedEmbeddingsRelatedByAutomorphism : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p] (n m : ℕ)
    (e₁ : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n)))
    [AlgebraicGeometry.IsClosedImmersion e₁]
    (e₂ : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m)))
    [AlgebraicGeometry.IsClosedImmersion e₂],
    e₁ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) = p →
    e₂ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin m)) = p →
    ∃ Φ : affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ≅
            affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)),
      Φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) =
          affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) ∧
        AffineSpace.homOfVector p (coordVectorInl n m e₁) ≫ Φ.hom =
          AffineSpace.homOfVector p (coordVectorInr n m e₂)
abbrev AffineResolutionRule : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], SequenceOfBlowups Y
def IsCompatibleWithOpenImmersions (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    [AlgebraicGeometry.IsReduced V] [AlgebraicGeometry.IsAffine V]
    (φ : V ⟶ Y) [AlgebraicGeometry.IsOpenImmersion φ],
    φ ≫ pY = pV → IsPullbackBlowupSequence φ (R k V pV) (R k Y pY)
def IsCompatibleWithEtaleCovers (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y W : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pW : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType pW] [AlgebraicGeometry.QuasiCompact pW]
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.IsAffine W]
    (φ : W ⟶ Y) [AlgebraicGeometry.Etale φ],
    φ ≫ pY = pW → (∀ y : ↥Y, ∃ w : ↥W, φ.base w = y) →
    IsStrictPullbackBlowupSeq φ (R k W pW) (R k Y pY)
def IsCompatibleWithFieldBaseChange (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (K : Type u) [Field K] [CharZero K] [Algebra k K]
    [AlgebraicGeometry.IsReduced (baseChange p K)]
    [AlgebraicGeometry.IsAffine (baseChange p K)],
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (R K (baseChange p K) (baseChangeToSpec p K)) (R k Y p)
def IsInducedByAffineRule (R : AffineResolutionRule.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (B : SequenceOfBlowups Y) : Prop :=
  ∀ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.IsAffine W]
    (φ : W ⟶ Y) [AlgebraicGeometry.Etale φ],
    φ ≫ p = q → (∀ y : ↥Y, ∃ w : ↥W, φ.base w = y) → IsStrictPullbackBlowupSeq φ (R k W q) B
def ExistsGluedBlowupSequence (R : AffineResolutionRule.{u}) : Prop :=
  IsCompatibleWithEtaleCovers R →
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y],
    ∃ B : SequenceOfBlowups Y, (∀ i, i < B.length → B.center i ≠ ⊤) ∧ IsInducedByAffineRule R k Y p B
def InducedRuleCompatibleWithFieldExtension (R : AffineResolutionRule.{u}) : Prop :=
  IsCompatibleWithOpenImmersions R → IsCompatibleWithFieldBaseChange R →
  ∀ F : ResolutionRule.{u},
    (∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X],
      IsInducedByAffineRule R k X f (F k X f)) →
    IsCompatibleWithFieldExtension F
end FunctorialResolution.EmbeddedResolution


