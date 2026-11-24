-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:19.343279+00:00
-- url     : https://prove2.me/theorems/6164afb8-2428-4fec-bb0e-f5ec31136de5
-- title:
--   Line Field
-- statement:
--   Definitions and structural lemmas for Line Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/LineField.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
abbrev L : Type := FractionRing (MvPolynomial (Fin 2) ℚ)
def xL (i : Fin 2) : L := algebraMap (MvPolynomial (Fin 2) ℚ) L (X i)
def u : L := xL 1 / xL 0
abbrev Ω : Type := ↥(IntermediateField.adjoin ℚ ({u} : Set L))
def gen : Ω := IntermediateField.AdjoinSimple.gen ℚ u
def yLine : (Σ _ : Unit, Fin 2) → Ω := fun p => if p.2 = 0 then 1 else gen
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line


