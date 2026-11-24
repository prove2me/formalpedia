-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothLocalChart
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothLocalChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:09.738608+00:00
-- url     : https://prove2.me/theorems/2a1c9f78-92ec-4a5c-873f-e1e87313ddeb
-- title:
--   Smooth Local Chart
-- statement:
--   Definitions and structural lemmas for Smooth Local Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothLocalChart.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRule
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
structure SmoothLocalChart {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
    {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
    (G : EmbeddingDatum k Y pY) (H : EmbeddingDatum k V pV) (u : V ⟶ Y) (y : ↥V) where
  func : Γ(H.ambient, ⊤)
  mem_domain : y ∈ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  isAffine_ambient : AlgebraicGeometry.IsAffine ambient
  smooth_ambientStruct : AlgebraicGeometry.Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : AlgebraicGeometry.LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : AlgebraicGeometry.QuasiCompact ambientStruct
  toAmbient : ambient ⟶ G.ambient
  smooth_toAmbient : AlgebraicGeometry.Smooth toAmbient
  comp_eq : toAmbient ≫ G.ambientStruct = ambientStruct
  imm : (H.emb ⁻¹ᵁ H.ambient.basicOpen func).toScheme ⟶ ambient
  isClosedImmersion_imm : AlgebraicGeometry.IsClosedImmersion imm
  isPullback :
    CategoryTheory.IsPullback imm ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u) toAmbient
      G.emb
namespace SmoothLocalChart
variable {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
  {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
  {G : EmbeddingDatum k Y pY} {H : EmbeddingDatum k V pV} {u : V ⟶ Y} {y : ↥V}
abbrev chartDomain (C : SmoothLocalChart G H u y) : V.Opens :=
  H.emb ⁻¹ᵁ H.ambient.basicOpen C.func
instance instIsAffineAmbient (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.IsAffine C.ambient := C.isAffine_ambient
instance instSmoothAmbientStruct (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.Smooth C.ambientStruct := C.smooth_ambientStruct
instance instLocallyOfFiniteTypeAmbientStruct (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.LocallyOfFiniteType C.ambientStruct :=
  C.locallyOfFiniteType_ambientStruct
instance instQuasiCompactAmbientStruct (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.QuasiCompact C.ambientStruct := C.quasiCompact_ambientStruct
instance instSmoothToAmbient (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.Smooth C.toAmbient := C.smooth_toAmbient
instance instIsClosedImmersionImm (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.IsClosedImmersion C.imm := C.isClosedImmersion_imm
end SmoothLocalChart
end FunctorialResolution.EmbeddedResolution
end


