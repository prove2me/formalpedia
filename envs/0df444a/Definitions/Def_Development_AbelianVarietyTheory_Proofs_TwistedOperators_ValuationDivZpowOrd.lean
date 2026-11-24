-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:50:46.788217+00:00
-- url     : https://prove2.me/theorems/ff763ffe-1dcd-4efe-b40f-98234ab7e2c6
-- title:
--   Valuation Div Zpow Ord
-- statement:
--   Definitions and structural lemmas for Valuation Div Zpow Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ValuationDivZpowOrd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
namespace GlobalTheory.LocalCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
end GlobalTheory.LocalCartan


