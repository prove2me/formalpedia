-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAnalyticOfTendsto
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAnalyticOfTendsto
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:58:00.375996+00:00
-- url     : https://prove2.me/theorems/48ab47ba-75d8-4ee4-b1c6-e15acf84bd4f
-- title:
--   Exists Analytic Of Tendsto
-- statement:
--   Definitions and structural lemmas for Exists Analytic Of Tendsto, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsAnalyticOfTendsto.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology
noncomputable section
namespace GlobalTheory.EllipticPoles
variable (L : PeriodPair)
end GlobalTheory.EllipticPoles


