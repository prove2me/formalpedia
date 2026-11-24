-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumn
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:32.681246+00:00
-- url     : https://prove2.me/theorems/ced4e2d8-675a-4780-aa37-8eb92afd0ecf
-- title:
--   Mem Fourier Jacobi Subgroup Iff Parabolic Mul Column
-- statement:
--   Definitions and structural lemmas for Mem Fourier Jacobi Subgroup Iff Parabolic Mul Column, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemFourierJacobiSubgroupIffParabolicMulColumn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
namespace GlobalTheory.RootEx.FourierJacobiGroup
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
end GlobalTheory.RootEx.FourierJacobiGroup


