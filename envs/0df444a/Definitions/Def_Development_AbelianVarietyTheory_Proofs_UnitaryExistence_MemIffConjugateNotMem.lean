-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemIffConjugateNotMem
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemIffConjugateNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:13.17362+00:00
-- url     : https://prove2.me/theorems/796143a0-37bc-4325-83ce-78654689b81c
-- title:
--   Mem Iff Conjugate Not Mem
-- statement:
--   Definitions and structural lemmas for Mem Iff Conjugate Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemIffConjugateNotMem.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.UnitFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.UnitFrame


