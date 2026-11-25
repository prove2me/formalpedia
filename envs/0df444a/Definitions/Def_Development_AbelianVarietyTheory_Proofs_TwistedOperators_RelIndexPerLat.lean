-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexPerLat
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexPerLat
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:46.373382+00:00
-- url     : https://prove2.me/theorems/c726bf87-80bc-449b-bbf8-5e0ca61c0b86
-- title:
--   Rel Index Per Lat
-- statement:
--   Definitions and structural lemmas for Rel Index Per Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexPerLat.lean

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
namespace GlobalTheory.RootEx.PerIndex
variable {k : Type} [Field k] [ValuativeRel k] {n : Type}
end GlobalTheory.RootEx.PerIndex


