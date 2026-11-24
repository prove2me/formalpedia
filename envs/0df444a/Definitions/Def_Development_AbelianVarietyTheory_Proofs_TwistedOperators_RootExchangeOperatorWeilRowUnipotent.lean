-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeOperatorWeilRowUnipotent
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeOperatorWeilRowUnipotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:27.216334+00:00
-- url     : https://prove2.me/theorems/07d30207-bbd4-4ad0-b60b-4f6720224b73
-- title:
--   Root Exchange Operator Weil Row Unipotent
-- statement:
--   Definitions and structural lemmas for Root Exchange Operator Weil Row Unipotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeOperatorWeilRowUnipotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
namespace GlobalTheory.RootEx.RowSign
open GlobalTheory.RootEx.Exchange
end GlobalTheory.RootEx.RowSign


