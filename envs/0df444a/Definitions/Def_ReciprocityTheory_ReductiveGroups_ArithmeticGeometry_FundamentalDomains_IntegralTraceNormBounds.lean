-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:36.273966+00:00
-- url     : https://prove2.me/theorems/30db1c0b-1087-4114-b3da-1fdfe9dc0332
-- title:
--   Integral Trace Norm Bounds
-- statement:
--   Definitions and structural lemmas for Integral Trace Norm Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IntegralTraceNormBounds.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
open NumberField InfinitePlace Module Submodule TraceIntegralBasis
open scoped ComplexConjugate Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (E) in

noncomputable def ed : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate (K := ℚ) (L := E)) (integralBasis E)
variable (E) in

noncomputable def bd (j : Free.ChooseBasisIndex ℤ (𝓞 E)) : VS E := iota E (2 * cc (ed E j))
end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds


