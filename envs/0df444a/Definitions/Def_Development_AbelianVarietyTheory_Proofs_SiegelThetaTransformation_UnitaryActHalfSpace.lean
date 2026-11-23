-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:41.675811+00:00
-- url     : https://prove2.me/theorems/4d0723fa-599a-4df3-b181-7db061bd2f9a
-- title:
--   Unitary Act Half Space
-- statement:
--   Definitions and structural lemmas for Unitary Act Half Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
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
namespace GlobalTheory.SW.HAct
section Cplx
variable {N : ℕ} {A B C D Z : Matrix (Fin N) (Fin N) ℂ}
end Cplx
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
end GlobalTheory.SW.HAct


