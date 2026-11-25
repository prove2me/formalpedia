-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsValuationEqZpow
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsValuationEqZpow
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:26.841432+00:00
-- url     : https://prove2.me/theorems/9905793e-cdbb-40a1-a448-9a3e184b82bd
-- title:
--   Exists Valuation Eq Zpow
-- statement:
--   Definitions and structural lemmas for Exists Valuation Eq Zpow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsValuationEqZpow.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
namespace GlobalTheory.StepData.NormalForm
section Plain
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
end Plain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.StepData.NormalForm


