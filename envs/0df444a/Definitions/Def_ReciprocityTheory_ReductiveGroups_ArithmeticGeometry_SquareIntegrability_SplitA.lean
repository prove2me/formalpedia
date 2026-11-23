-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:06.114532+00:00
-- url     : https://prove2.me/theorems/e669d02d-5c22-48f1-a762-b2fba14eede9
-- title:
--   Split A
-- statement:
--   Definitions and structural lemmas for Split A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
section basic
variable {ι : Type} [Fintype ι]
end basic
variable {E : Type} [Field E] [NumberField E]
section vecU
variable {dim : (E →+* ℂ) → ℕ}
end vecU
end
end ReciprocityTheory.ChartRestriction.G.I2


