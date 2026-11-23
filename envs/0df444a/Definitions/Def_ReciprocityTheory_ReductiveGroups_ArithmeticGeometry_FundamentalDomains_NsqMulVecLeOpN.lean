-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NsqMulVecLeOpN
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NsqMulVecLeOpN
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:25:07.953801+00:00
-- url     : https://prove2.me/theorems/5988d618-55ce-48ed-863a-2e484765754e
-- title:
--   Nsq Mul Vec Le Op N
-- statement:
--   Definitions and structural lemmas for Nsq Mul Vec Le Op N, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/NsqMulVecLeOpN.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
def nsq {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ j, ‖v j‖ ^ 2
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds


