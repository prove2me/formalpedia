-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:36.289389+00:00
-- url     : https://prove2.me/theorems/79710faa-d154-4ab0-9270-ab7228cb4151
-- title:
--   Unipotent Sub One Majorant Bound
-- statement:
--   Definitions and structural lemmas for Unipotent Sub One Majorant Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
section perTau
variable {x : Frame X.Ψ r} {τ : X.Ψ}
variable {e : Fin r → ℂ} (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ) (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0)
  (hq : X.d2q x τ e ≠ 0) (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
include hx he hq hself
end perTau
end Data
end ReciprocityTheory.ChartRestriction.G.FD


