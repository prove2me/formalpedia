-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:08.177712+00:00
-- url     : https://prove2.me/theorems/63524bd4-e57b-4b85-ac8b-040062d8fd12
-- title:
--   Flow Matrix Majorants
-- statement:
--   Definitions and structural lemmas for Flow Matrix Majorants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatrixMajorants.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
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
namespace FlowMatrixMajorants
open MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)
end FlowMatrixMajorants
end ReciprocityTheory.ChartRestriction.G.FD


