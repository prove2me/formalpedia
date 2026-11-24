-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:45.842889+00:00
-- url     : https://prove2.me/theorems/c28b269d-286f-4175-bd17-eaf1742ed093
-- title:
--   Int Ind Pow
-- statement:
--   Definitions and structural lemmas for Int Ind Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/IntIndPow.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
namespace PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open Classical in

def dl (ν : kˣ →* ℂˣ) (x : k) : ℂ :=
  if h : x ≠ 0 ∧ valuation k x = 1 then (((ν (Units.mk0 x h.1))⁻¹ : ℂˣ) : ℂ) else 0
variable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
def gI (m : Measure k) (ψ : AddChar k ℂ) (ν : kˣ →* ℂˣ) (y : k) : ℂ := ∫ r, dl ν r * ψ (y * r) ∂m
end PositivityTheory.ThKG.Std


