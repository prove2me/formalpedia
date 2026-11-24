-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinates
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:46.994064+00:00
-- url     : https://prove2.me/theorems/a963e038-8992-4c79-8870-1bdfa6b2d004
-- title:
--   PBirational Coordinates
-- statement:
--   Definitions and structural lemmas for PBirational Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinates.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
namespace BirationalCoordinates
section Ratios
variable {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]
def ratioField (x : Ix κ → Ω) (c : κ) : Subfield Ω :=
  Subfield.closure (Set.range fun p : Ix κ => x p / x ⟨(), c⟩)
def ratios (x : Ix κ → Ω) (c : κ) : Ix κ → ratioField x c := fun p =>
  ⟨x p / x ⟨(), c⟩, Subfield.subset_closure ⟨p, rfl⟩⟩
end Ratios
end BirationalCoordinates
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


