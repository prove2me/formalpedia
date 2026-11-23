-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ImaginaryMajorants
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ImaginaryMajorants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:20.063123+00:00
-- url     : https://prove2.me/theorems/620c905d-6827-4159-a713-6c2b0f067713
-- title:
--   Imaginary Majorants
-- statement:
--   Definitions and structural lemmas for Imaginary Majorants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ImaginaryMajorants.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
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
namespace ImaginaryMajorants
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds
variable {r : ℕ} (X : Data E r)
end ImaginaryMajorants
end ReciprocityTheory.ChartRestriction.G.FD


