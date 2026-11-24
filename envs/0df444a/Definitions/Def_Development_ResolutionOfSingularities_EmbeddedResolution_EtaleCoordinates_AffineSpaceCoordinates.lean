-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:33.409799+00:00
-- url     : https://prove2.me/theorems/37ddcce6-1706-4cd5-9e8c-78ea21c77ed9
-- title:
--   Affine Space Coordinates
-- statement:
--   Definitions and structural lemmas for Affine Space Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/AffineSpaceCoordinates.lean

import Mathlib
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
abbrev affineSpaceIndexedBy (k : Type u) [Field k] (n : Type u) : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace n (Spec (CommRingCat.of k))
abbrev affineSpaceIndexedByToSpec (k : Type u) [Field k] (n : Type u) :
    affineSpaceIndexedBy k n ⟶ Spec (CommRingCat.of k) :=
  affineSpaceIndexedBy k n ↘ Spec (CommRingCat.of k)
def pullbackCoord {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) : Γ(Y, ⊤) :=
  f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i)
def coordVectorInl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun a => pullbackCoord f (ULift.up a)) (fun _ => 0) i.down
def coordVectorInr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun _ => 0) (fun b => pullbackCoord f (ULift.up b)) i.down
end FunctorialResolution.EmbeddedResolution


