-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:05.132602+00:00
-- url     : https://prove2.me/theorems/0043524d-5f9a-430b-8629-7778a09bfa69
-- title:
--   Discr Mul Hermitian Integral
-- statement:
--   Definitions and structural lemmas for Discr Mul Hermitian Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace DataX
variable {r : ℕ} (X : DataX E r)
noncomputable def c0E : E := ((X.g * dEnat E : ℕ) : E) / 2
end DataX
end ReciprocityTheory.ChartRestriction.G.FD


