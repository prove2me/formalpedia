-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ElementaryDivisorStatement
-- name    : ReciprocityTheory_DualLattices_ElementaryDivisorStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:48.696708+00:00
-- url     : https://prove2.me/theorems/f4cc5b73-d5bc-421a-9a62-e11a73b8aae3
-- title:
--   Elementary Divisor Statement
-- statement:
--   Definitions and structural lemmas for Elementary Divisor Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ElementaryDivisorStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroupStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ED
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
end ED
end ReciprocityTheory.PGsh.Up


