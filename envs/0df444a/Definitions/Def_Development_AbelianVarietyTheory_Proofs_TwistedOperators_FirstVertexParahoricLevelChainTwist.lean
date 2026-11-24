-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwist
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwist
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:02:00.418105+00:00
-- url     : https://prove2.me/theorems/e7f76f2c-8aea-4691-92ad-a769f7651df9
-- title:
--   First Vertex Parahoric Level Chain Twist
-- statement:
--   Definitions and structural lemmas for First Vertex Parahoric Level Chain Twist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexParahoricLevelChainTwist.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
namespace GlobalTheory.TwistVertex
section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
end Plain
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
section General
variable {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
end General
section Empty
variable {r e n : Type*} [Fintype r] [DecidableEq r] [Fintype e] [DecidableEq e] [IsEmpty e]
  [Fintype n] [DecidableEq n] {c : ℕ} {δ : kˣ →* ℂˣ} {hδ : IsTame δ}
end Empty
end GlobalTheory.TwistVertex


