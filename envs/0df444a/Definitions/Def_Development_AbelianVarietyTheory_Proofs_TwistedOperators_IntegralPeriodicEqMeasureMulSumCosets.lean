-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralPeriodicEqMeasureMulSumCosets
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralPeriodicEqMeasureMulSumCosets
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:49.550114+00:00
-- url     : https://prove2.me/theorems/fee64f10-eea1-5e37-9a95-909a6b2d1467
-- title:
--   Integral Periodic Eq Measure Mul Sum Cosets
-- statement:
--   Definitions and structural lemmas for Integral Periodic Eq Measure Mul Sum Cosets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralPeriodicEqMeasureMulSumCosets.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
namespace GlobalTheory.RootEx.UnfoldShape
end GlobalTheory.RootEx.UnfoldShape


