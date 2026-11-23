-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:08.53395+00:00
-- url     : https://prove2.me/theorems/68d78b8f-018e-411f-81e9-15dc66a8294c
-- title:
--   Quadratic Coefficient Forms
-- statement:
--   Definitions and structural lemmas for Quadratic Coefficient Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticCoefficientForms.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
def toCP (τ : X.Ψ) : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩
end
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms


