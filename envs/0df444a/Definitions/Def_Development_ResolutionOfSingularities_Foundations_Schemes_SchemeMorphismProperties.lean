-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
-- name    : Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:46.677424+00:00
-- url     : https://prove2.me/theorems/7fb3f23c-64f9-404c-a674-69ef8606616e
-- title:
--   Scheme Morphism Properties
-- statement:
--   Definitions and structural lemmas for Scheme Morphism Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace FunctorialResolution.Blowup
theorem small_directedAffineCover_I₀ (X : Scheme.{u}) :
    Small.{u} X.directedAffineCover.I₀ :=
  small_self _
instance instSmallDirectedAffineCoverI₀ (X : Scheme.{u}) :
    Small.{u} X.directedAffineCover.I₀ :=
  small_directedAffineCover_I₀ X
theorem isThin_directedAffineCover_I₀ (X : Scheme.{u}) :
    Quiver.IsThin X.directedAffineCover.I₀ := by
  intro a b
  refine ⟨fun f g => ?_⟩
  obtain ⟨⟨hf⟩⟩ := f
  obtain ⟨⟨hg⟩⟩ := g
  rfl
instance instIsThinDirectedAffineCoverI₀ (X : Scheme.{u}) :
    Quiver.IsThin X.directedAffineCover.I₀ :=
  isThin_directedAffineCover_I₀ X
theorem noetherianSpace_toScheme (X : Scheme.{u}) [NoetherianSpace ↥X] (U : X.Opens) :
    NoetherianSpace ↥(U.toScheme) := by
  have h : Topology.IsInducing (fun x : { y : ↥X // y ∈ U } => (x : ↥X)) := ⟨rfl⟩
  exact h.noetherianSpace
instance instNoetherianSpaceToScheme (X : Scheme.{u}) [NoetherianSpace ↥X] (U : X.Opens) :
    NoetherianSpace ↥(U.toScheme) :=
  noetherianSpace_toScheme X U
theorem isAffineHom_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    AlgebraicGeometry.IsAffineHom (Spec.map φ) :=
  inferInstance
theorem isAffineHom_pullback_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [AlgebraicGeometry.IsAffineHom g] :
    AlgebraicGeometry.IsAffineHom (pullback.fst f g) :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsAffineHom)
    (IsPullback.of_hasPullback f g).flip ‹AlgebraicGeometry.IsAffineHom g›
theorem isAffineHom_pullback_fst_specMap_of_field {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    AlgebraicGeometry.IsAffineHom (pullback.fst p (Spec.map φ)) :=
  @isAffineHom_pullback_fst X _ _ p (Spec.map φ) (isAffineHom_specMap φ)
instance instIsAffineHomSpecMapPullbackFst {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    AlgebraicGeometry.IsAffineHom (pullback.fst p (Spec.map φ)) :=
  isAffineHom_pullback_fst_specMap_of_field p φ
end FunctorialResolution.Blowup
namespace TopologicalSpace.NoetherianSpace
end TopologicalSpace.NoetherianSpace
namespace AlgebraicGeometry
namespace Scheme
namespace Hom
end Hom
end Scheme
end AlgebraicGeometry


