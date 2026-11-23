-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:51.166517+00:00
-- url     : https://prove2.me/theorems/fc6454e7-7323-49f7-a644-85c05c10bd5b
-- title:
--   Majorant Conjugate Transfer
-- statement:
--   Definitions and structural lemmas for Majorant Conjugate Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantConjugateTransfer.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
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
namespace MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r)
end MajorantConjugateTransfer
end ReciprocityTheory.ChartRestriction.G.FD


