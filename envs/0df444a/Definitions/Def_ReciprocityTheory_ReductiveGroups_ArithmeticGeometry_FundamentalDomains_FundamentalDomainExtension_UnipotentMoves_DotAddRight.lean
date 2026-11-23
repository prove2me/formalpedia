-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:48.956929+00:00
-- url     : https://prove2.me/theorems/c589ebf3-e539-4f39-b6bb-26918253f38f
-- title:
--   Dot Add Right
-- statement:
--   Definitions and structural lemmas for Dot Add Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/DotAddRight.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UnipMove.MajH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
def dot {n : ℕ} (u w : Fin n → ℂ) : ℂ := ∑ i, u i * conj (w i)
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
end Frames
end
end UnipMove.MajH
namespace UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
end UnipMove


