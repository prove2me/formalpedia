-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:27.315027+00:00
-- url     : https://prove2.me/theorems/3e1c22a5-d4c4-4aa2-b9a9-a3c979d56a83
-- title:
--   Quad Cocycle
-- statement:
--   Definitions and structural lemmas for Quad Cocycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/QuadCocycle.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.HermComp
variable {N : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.SW.HermComp


