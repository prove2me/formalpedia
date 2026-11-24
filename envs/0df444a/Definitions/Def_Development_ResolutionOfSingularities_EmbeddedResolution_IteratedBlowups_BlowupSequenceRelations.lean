-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:22.214043+00:00
-- url     : https://prove2.me/theorems/f36f6705-6c2a-4ce2-baf1-fb413180e804
-- title:
--   Blowup Sequence Relations
-- statement:
--   Definitions and structural lemmas for Blowup Sequence Relations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceRelations.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
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
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def imageIdealSheaf {S X : Scheme.{u}} (σ : S ⟶ X) (I : S.IdealSheafData) : X.IdealSheafData :=
  (I.subschemeι ≫ σ).ker
def SequenceOfBlowups.Isomorphic {X : Scheme.{u}} (B B' : SequenceOfBlowups X) : Prop :=
  B.length = B'.length ∧
    ∃ e : ∀ i : ℕ, i ≤ B.length → (B.schemeAt i ≅ B'.schemeAt i),
      ((e 0 (Nat.zero_le _)).hom ≫ B'.isoZero.hom = B.isoZero.hom) ∧
      (∀ i : ℕ, ∀ hi : i < B.length,
        (e (i + 1) hi).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hi.le).hom) ∧
      (∀ i : ℕ, ∀ hi : i < B.length,
        (B'.center i).comap (e i hi.le).hom = B.center i)
def IsPushforwardBlowupSeq {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X) : Prop :=
  BS.length = B.length ∧
    ∃ σ : ∀ i : ℕ, i ≤ BS.length → (BS.schemeAt i ⟶ B.schemeAt i),
      (∀ i : ℕ, ∀ hi : i ≤ BS.length, IsClosedImmersion (σ i hi)) ∧
      (σ 0 (Nat.zero_le _) ≫ B.isoZero.hom = BS.isoZero.hom ≫ j) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        σ (i + 1) hi ≫ B.transitionMapSucc i = BS.transitionMapSucc i ≫ σ i hi.le) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        B.center i = imageIdealSheaf (σ i hi.le) (BS.center i)) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        (σ (i + 1) hi).ker =
          Blowup.strictTransform (B.transitionMapSucc i) (B.center i) (σ i hi.le).ker)
def IsStrictPullbackBlowupSeq {X' X : Scheme.{u}} (φ : X' ⟶ X)
    (B' : SequenceOfBlowups X') (B : SequenceOfBlowups X) : Prop :=
  B'.length = B.length ∧
    ∃ σ : ∀ i : ℕ, i ≤ B'.length → (B'.schemeAt i ⟶ B.schemeAt i),
      (σ 0 (Nat.zero_le _) ≫ B.isoZero.hom = B'.isoZero.hom ≫ φ) ∧
      (∀ i : ℕ, ∀ hi : i < B'.length,
        IsPullback (σ (i + 1) hi) (B'.transitionMapSucc i) (B.transitionMapSucc i) (σ i hi.le)) ∧
      (∀ i : ℕ, ∀ hi : i < B'.length,
        B'.center i = (B.center i).comap (σ i hi.le))
def schemeAtHomOfEqZero {X' X : Scheme.{u}} (g : X' ⟶ X) (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
    (i : ℕ) (hi0 : i = 0) : t.schemeAt i ⟶ s.schemeAt i :=
  eqToHom (congrArg t.schemeAt hi0) ≫ t.isoZero.hom ≫ g ≫ s.isoZero.inv ≫
    eqToHom (congrArg s.schemeAt hi0).symm
end FunctorialResolution.EmbeddedResolution


