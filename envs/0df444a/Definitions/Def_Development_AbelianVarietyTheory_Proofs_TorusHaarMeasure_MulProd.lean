-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MulProd
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MulProd
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:16:58.065219+00:00
-- url     : https://prove2.me/theorems/84a5164a-161f-4d7c-8d11-ee81efb9907e
-- title:
--   Mul Prod
-- statement:
--   Definitions and structural lemmas for Mul Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MulProd.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
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
namespace GlobalTheory.LeadBound
open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
section
variable {r : ℕ} (X : Data E r) (g : Frame X.Ψ r → ℝ)
def IsDom (la : Wt X.Ψ r) (n : ℕ) (P : Frame X.Ψ r → ℂ) : Prop :=
  X.IsBddSec la P ∧ ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C * g x ^ n
variable {X g}
end
end GlobalTheory.LeadBound


