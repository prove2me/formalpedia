-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:09.81132+00:00
-- url     : https://prove2.me/theorems/a26dfa0c-01d9-4812-acce-bc0ede03a7ef
-- title:
--   Finrank Eq Two Mul Half Degree
-- statement:
--   Definitions and structural lemmas for Finrank Eq Two Mul Half Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
end Data
end
end ReciprocityTheory.ChartRestriction.G.FD


