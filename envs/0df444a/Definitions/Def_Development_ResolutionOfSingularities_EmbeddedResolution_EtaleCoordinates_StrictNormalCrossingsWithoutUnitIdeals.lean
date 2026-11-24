-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsWithoutUnitIdeals
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsWithoutUnitIdeals
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:07:05.999697+00:00
-- url     : https://prove2.me/theorems/55ea6283-3f4a-44c2-ad04-6fc0071b8b83
-- title:
--   Strict Normal Crossings Without Unit Ideals
-- statement:
--   Definitions and structural lemmas for Strict Normal Crossings Without Unit Ideals, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsWithoutUnitIdeals.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
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
variable {X : Scheme.{u}} {k : Type u} [Field k]
noncomputable def filterNeTop (E : List X.IdealSheafData) : List X.IdealSheafData :=
  E.filter (fun D => @decide (D ≠ ⊤) (Classical.propDecidable _))
def unshiftIndex (g₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => g₀ i
def shiftIndex (g₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => g₀ i + 1
open Classical in
def transportAssignment {m : ℕ} (E' : List X.IdealSheafData) (a : ℕ → Option (Fin m))
    (g : ℕ → ℕ) : ℕ → Option (Fin m) :=
  fun i => if E'[i]? = some ⊤ then none else a (g i)
end FunctorialResolution.EmbeddedResolution


