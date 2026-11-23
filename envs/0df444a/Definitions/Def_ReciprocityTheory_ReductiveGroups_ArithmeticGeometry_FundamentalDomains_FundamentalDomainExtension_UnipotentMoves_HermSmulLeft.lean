-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermSmulLeft
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermSmulLeft
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:12.919453+00:00
-- url     : https://prove2.me/theorems/b67a73f0-2195-4730-aa54-62be3fb73eb9
-- title:
--   Herm Smul Left
-- statement:
--   Definitions and structural lemmas for Herm Smul Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/HermSmulLeft.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end UnipMove


