-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_FieldExtensionEtaleCover
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_FieldExtensionEtaleCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:44.68285+00:00
-- url     : https://prove2.me/theorems/f41838b5-65a3-4d51-81ac-ff2664f88bab
-- title:
--   Field Extension Etale Cover
-- statement:
--   Definitions and structural lemmas for Field Extension Etale Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/FieldExtensionEtaleCover.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
noncomputable section
variable {k : Type u} [Field k] {X W : Scheme.{u}}
theorem pullbackCondition_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    (baseChangeProjection (c ≫ f) K ≫ c) ≫ f = baseChangeToSpec (c ≫ f) K ≫ specMapAlgebraMap k K := by
  rw [Category.assoc]
  exact pullback.condition
def baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChange (c ≫ f) K ⟶ baseChange f K :=
  pullback.lift (baseChangeProjection (c ≫ f) K ≫ c) (baseChangeToSpec (c ≫ f) K)
    (pullbackCondition_baseChangeMap f c K)
@[simp]
theorem baseChangeMap_comp_baseChangeProjection (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChangeMap f c K ≫ baseChangeProjection f K = baseChangeProjection (c ≫ f) K ≫ c :=
  pullback.lift_fst _ _ _
@[simp]
theorem baseChangeMap_comp_baseChangeToSpec (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChangeMap f c K ≫ baseChangeToSpec f K = baseChangeToSpec (c ≫ f) K :=
  pullback.lift_snd _ _ _
theorem morphismProperty_of_isPullback {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {A B C' D : Scheme.{u}} {h : A ⟶ B} {v : A ⟶ C'} {v' : B ⟶ D}
    {b : C' ⟶ D} (sq : IsPullback h v v' b) (hb : P b) : P h :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hb
theorem isPullback_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    IsPullback (baseChangeMap f c K) (baseChangeProjection (c ≫ f) K) (baseChangeProjection f K) c := by
  have h1 : IsPullback (baseChangeToSpec (c ≫ f) K) (baseChangeProjection (c ≫ f) K)
      (specMapAlgebraMap k K) (c ≫ f) := (IsPullback.of_hasPullback (c ≫ f) (specMapAlgebraMap k K)).flip
  have h2 : IsPullback (baseChangeToSpec f K) (baseChangeProjection f K) (specMapAlgebraMap k K) f :=
    (IsPullback.of_hasPullback f (specMapAlgebraMap k K)).flip
  refine IsPullback.of_right ?_ (baseChangeMap_comp_baseChangeProjection f c K) h2
  rw [baseChangeMap_comp_baseChangeToSpec]
  exact h1
theorem etale_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Etale c]
    (K : Type u) [Field K] [Algebra k K] : Etale (baseChangeMap f c K) :=
  morphismProperty_of_isPullback (P := @Etale) (isPullback_baseChangeMap f c K) ‹Etale c›
instance instEtaleBaseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Etale c]
    (K : Type u) [Field K] [Algebra k K] : Etale (baseChangeMap f c K) :=
  etale_baseChangeMap f c K
theorem surjective_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Surjective c]
    (K : Type u) [Field K] [Algebra k K] : Surjective (baseChangeMap f c K) :=
  morphismProperty_of_isPullback (P := @Surjective) (isPullback_baseChangeMap f c K) ‹Surjective c›
instance instSurjectiveBaseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Surjective c]
    (K : Type u) [Field K] [Algebra k K] : Surjective (baseChangeMap f c K) :=
  surjective_baseChangeMap f c K
end
end FunctorialResolution.EmbeddedResolution


