-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:57.946172+00:00
-- url     : https://prove2.me/theorems/f9d8745f-df93-4713-89bc-907d24310a3c
-- title:
--   Gram Flow Transform
-- statement:
--   Definitions and structural lemmas for Gram Flow Transform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramFlowTransform.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E}
def flw (α : ℂ) (e : Fin r → ℂ) (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (f : Fin n → Fin r → ℂ) : Fin n → Fin r → ℂ :=
  fun a => f a + (α * hermC τ G (f a) e) • e
end
end ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform


