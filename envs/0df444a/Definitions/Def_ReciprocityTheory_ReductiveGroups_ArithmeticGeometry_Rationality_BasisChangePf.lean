-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:26.270071+00:00
-- url     : https://prove2.me/theorems/eee2002a-6b15-4eb6-9923-b067e6ae6986
-- title:
--   Basis Change Pf
-- statement:
--   Definitions and structural lemmas for Basis Change Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BasisChangePf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangeSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
namespace BasisChangePf
open MvPolynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}
def CB (Q : MvPolynomial ι K) (c : ℝ) : Prop := ∀ μ, ‖coeff μ Q‖ ≤ c
end BasisChangePf
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


