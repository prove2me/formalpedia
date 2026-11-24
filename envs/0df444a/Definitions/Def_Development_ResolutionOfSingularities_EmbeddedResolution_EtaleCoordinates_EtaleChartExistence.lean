-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:46.940695+00:00
-- url     : https://prove2.me/theorems/be949d4c-a8ef-46ba-a404-2ddf9c4e5283
-- title:
--   Etale Chart Existence
-- statement:
--   Definitions and structural lemmas for Etale Chart Existence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartExistence.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
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
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
theorem homOfLE_comp_map_comp_affineSpaceFinToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : X.Opens} (hVU : V ≤ U) :
    (X.homOfLE hVU ≫ c.map) ≫ affineSpaceFinToSpec k m = V.ι ≫ p := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.homOfLE_ι]
theorem etale_homOfLE_comp_map {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : X.Opens} (hVU : V ≤ U) :
    AlgebraicGeometry.Etale (X.homOfLE hVU ≫ c.map) := by
  have := c.isEtale
  infer_instance
def EtaleChart.restrict {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : X.Opens} (hVU : V ≤ U) : EtaleChart p V m where
  map := X.homOfLE hVU ≫ c.map
  comp_struct := homOfLE_comp_map_comp_affineSpaceFinToSpec c hVU
  isEtale := etale_homOfLE_comp_map c hVU
@[simp]
theorem EtaleChart.restrict_map {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : X.Opens} (hVU : V ≤ U) :
    (c.restrict hVU).map = X.homOfLE hVU ≫ c.map := rfl
theorem homOfVector_comp_affineSpaceFinToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) {m : ℕ}
    (v : ULift.{u} (Fin m) → U.toScheme.presheaf.obj (op ⊤)) :
    AffineSpace.homOfVector (U.ι ≫ p) v ≫ affineSpaceFinToSpec k m = U.ι ≫ p := by
  simp
def EtaleChart.ofCoords {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) {m : ℕ}
    (v : ULift.{u} (Fin m) → U.toScheme.presheaf.obj (op ⊤))
    (he : AlgebraicGeometry.Etale (AffineSpace.homOfVector (U.ι ≫ p) v)) :
    EtaleChart p U m where
  map := AffineSpace.homOfVector (U.ι ≫ p) v
  comp_struct := homOfVector_comp_affineSpaceFinToSpec p U v
  isEtale := he
end FunctorialResolution.EmbeddedResolution


