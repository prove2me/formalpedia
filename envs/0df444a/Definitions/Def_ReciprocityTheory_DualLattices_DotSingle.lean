-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
-- name    : ReciprocityTheory_DualLattices_DotSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:10.130544+00:00
-- url     : https://prove2.me/theorems/1aad9625-4c47-4e43-877a-7dfadaf517d2
-- title:
--   Dot Single
-- statement:
--   Definitions and structural lemmas for Dot Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DotSingle.lean

import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
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
namespace ReciprocityTheory.PGsh.Up.ED
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
end ReciprocityTheory.PGsh.Up.ED


