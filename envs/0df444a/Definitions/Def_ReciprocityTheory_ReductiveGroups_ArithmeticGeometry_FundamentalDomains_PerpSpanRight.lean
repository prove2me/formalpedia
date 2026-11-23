-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:41.656992+00:00
-- url     : https://prove2.me/theorems/19e5c754-ca03-4d4c-ad32-002fcacab27f
-- title:
--   Perp Span Right
-- statement:
--   Definitions and structural lemmas for Perp Span Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
def hL (v : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun u := hermC τ G u v
  map_add' u u' := hermC_add_left τ G u u' v
  map_smul' c u := by simp [hermC_smul_left]
variable (hG : ∀ a b, cc (G a b) = G b a)
include hG
end
end ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary


