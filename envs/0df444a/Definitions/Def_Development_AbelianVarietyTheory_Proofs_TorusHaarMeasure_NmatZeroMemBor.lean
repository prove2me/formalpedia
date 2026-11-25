-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NmatZeroMemBor
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NmatZeroMemBor
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:23:02.041493+00:00
-- url     : https://prove2.me/theorems/badb6a2f-5bf6-4453-8bc9-0444ffe3e865
-- title:
--   Nmat Zero Mem Bor
-- statement:
--   Definitions and structural lemmas for Nmat Zero Mem Bor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/NmatZeroMemBor.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics
namespace GlobalTheory.LeadJets
noncomputable section
def leadVal {n δ : ℕ} (s : Fin n → ℂ) (w : ℂ) (t : Fin δ → ℂ) (T a0 : ℕ)
    (cc : (Fin n → ℕ) → Fin δ → ℂ) : ℂ :=
  ∑ α ∈ multiLt n a0, ∑ k, cc α k * (∏ q, s q ^ α q) * w ^ (T - ∑ q, α q) * t k
section Step
variable {n δ m : ℕ} {U : Fin m → Set (V n)} {f w : Fin m → V n → ℂ}
  {s : Fin m → V n → Fin n → ℂ} {t : Fin m → V n → Fin δ → ℂ}
end Step
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end
end GlobalTheory.LeadJets


