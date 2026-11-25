-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:32:38.658101+00:00
-- url     : https://prove2.me/theorems/2fc59a25-9ba3-409e-8edd-6e705ff90d95
-- title:
--   Continuous Inv Leading Block Entry
-- statement:
--   Definitions and structural lemmas for Continuous Inv Leading Block Entry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq

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
namespace GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
section Calculus
variable {n : ℕ}
def SharpAt (φ : V n → ℝ) (x : V n) (ξ : Fin n → ℂ) : Prop :=
  ContDiffAt ℝ 2 φ x ∧ 0 ≤ φ x ∧ 0 ≤ (leviV n (fun y => (φ y : ℂ)) x ξ).re ∧
    Complex.normSq (∑ j, wd n j (fun y => (φ y : ℂ)) x * ξ j) ≤
      φ x * (leviV n (fun y => (φ y : ℂ)) x ξ).re
end Calculus
section Matrices
end Matrices
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.SharpGradient


