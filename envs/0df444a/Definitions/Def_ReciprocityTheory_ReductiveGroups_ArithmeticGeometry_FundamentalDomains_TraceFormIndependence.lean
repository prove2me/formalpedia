-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:29.176335+00:00
-- url     : https://prove2.me/theorems/33f217c4-a9ea-448f-9985-7b3f9be8114b
-- title:
--   Trace Form Independence
-- statement:
--   Definitions and structural lemmas for Trace Form Independence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
noncomputable def efr (X : Data E r) (v w : X.Ψ → Fin r → ℂ) : ℝ :=
  ∑ τ, 2 * (τ.1 (-X.ξ0) * hermC τ.1 X.Gm (v τ) (w τ)).re
end ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence


