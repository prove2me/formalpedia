-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:21.469223+00:00
-- url     : https://prove2.me/theorems/0ace9459-b456-53ef-8726-ec8eac3d9edc
-- title:
--   Zpow Mul Mem Pow
-- statement:
--   Definitions and structural lemmas for Zpow Mul Mem Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
namespace GlobalTheory.LatClass
section Pow
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hϖ : valuation k (ϖ : k) = uniformizer k)
include hϖ
end Pow
section Lat
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Lat
end GlobalTheory.LatClass


