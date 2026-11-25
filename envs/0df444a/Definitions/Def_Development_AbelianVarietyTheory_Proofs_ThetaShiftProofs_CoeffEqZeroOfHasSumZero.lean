-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CoeffEqZeroOfHasSumZero
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CoeffEqZeroOfHasSumZero
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:39.266259+00:00
-- url     : https://prove2.me/theorems/a1635933-45a6-465e-aabf-6465b73cc951
-- title:
--   Coeff Eq Zero Of Has Sum Zero
-- statement:
--   Definitions and structural lemmas for Coeff Eq Zero Of Has Sum Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.LaurentFJ
open Complex ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
end
end GlobalTheory.LaurentFJ


