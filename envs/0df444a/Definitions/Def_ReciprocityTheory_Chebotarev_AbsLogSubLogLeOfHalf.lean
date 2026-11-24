-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
-- name    : ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:11.16179+00:00
-- url     : https://prove2.me/theorems/f44db522-3bad-4dec-8eca-746017d40523
-- title:
--   Abs Log Sub Log Le Of Half
-- statement:
--   Definitions and structural lemmas for Abs Log Sub Log Le Of Half, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
namespace ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
section Core
variable {y k : mixedSpace E} {B a : ℝ}
end Core
end ReciprocityTheory.Cheb


