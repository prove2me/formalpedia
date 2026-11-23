-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:36.260866+00:00
-- url     : https://prove2.me/theorems/b0e3c68d-a1bd-4baa-97b4-df621f751e5b
-- title:
--   Embedding Herm Self
-- statement:
--   Definitions and structural lemmas for Embedding Herm Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EmbeddingHermSelf.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace TraceDualMin
end TraceDualMin
end GlobalTheory


