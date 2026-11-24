-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:33.456414+00:00
-- url     : https://prove2.me/theorems/0faba8ea-9f73-430d-a113-b3d60efd0b9a
-- title:
--   Disjoint Union Of Opens
-- statement:
--   Definitions and structural lemmas for Disjoint Union Of Opens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
universe u
noncomputable abbrev sigmaOpens (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) : Scheme.{u} :=
  ∐ fun i => (U i).toScheme
noncomputable abbrev sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    sigmaOpens Y U ⟶ Y :=
  Sigma.desc fun i => (U i).ι
theorem isReduced_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] [_root_.IsReduced B] (e : A ≃+* B) :
    _root_.IsReduced A :=
  ⟨fun _ hx => e.injective (((hx.map e).eq_zero).trans (map_zero e).symm)⟩
theorem isReduced_of_forall_isReduced_stalk (X : Scheme.{u})
    (h : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)) : IsReduced X := by
  have := h
  exact isReduced_of_isReduced_stalk X
theorem isReduced_sigmaOpens (Y : Scheme.{u}) [IsReduced Y] {ι : Type u} (U : ι → Y.Opens) :
    IsReduced (sigmaOpens Y U) := by
  refine isReduced_of_forall_isReduced_stalk _ ?_
  intro x
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk fun i => (U i).toScheme).surjective x
  have hx' : (Sigma.ι (fun i => (U i).toScheme) i).base y = x := by simpa using hx
  subst hx'
  exact isReduced_of_ringEquiv
    (((asIso ((Sigma.ι (fun i => (U i).toScheme) i).stalkMap y)).commRingCatIsoToRingEquiv).trans
      ((asIso (((U i).ι).stalkMap y)).commRingCatIsoToRingEquiv.symm))
instance instIsReducedOpensCoprod (Y : Scheme.{u}) [IsReduced Y] {ι : Type u} (U : ι → Y.Opens) :
    IsReduced (sigmaOpens Y U) :=
  isReduced_sigmaOpens Y U
theorem etale_isZariskiLocalAtSource : IsZariskiLocalAtSource (@Etale.{u}) := by
  have hrh : HasRingHomProperty (@Etale.{u}) RingHom.Etale := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Etale.{u}) _ hrh
theorem etale_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    Etale (sigmaOpensDesc Y U) := by
  have hloc : IsZariskiLocalAtSource (@Etale.{u}) := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
instance instEtaleOpensCoprodDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    Etale (sigmaOpensDesc Y U) :=
  etale_sigmaOpensDesc Y U
theorem locallyOfFiniteType_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    LocallyOfFiniteType (sigmaOpensDesc Y U) := by
  have : Etale (sigmaOpensDesc Y U) := etale_sigmaOpensDesc Y U
  infer_instance
instance instLocallyOfFiniteTypeOpensCoprodDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    LocallyOfFiniteType (sigmaOpensDesc Y U) :=
  locallyOfFiniteType_sigmaOpensDesc Y U
theorem smooth_isZariskiLocalAtSource : IsZariskiLocalAtSource (@Smooth.{u}) := by
  have hrh : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{u}) _ hrh
instance instIsZariskiLocalAtSourceSmooth : IsZariskiLocalAtSource (@Smooth.{u}) :=
  smooth_isZariskiLocalAtSource
end FunctorialResolution.EmbeddedResolution


