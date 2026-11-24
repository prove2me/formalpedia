-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfLinearIndependent
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfLinearIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:29.602965+00:00
-- url     : https://prove2.me/theorems/dfc873a6-60b6-4bb4-81ff-092df3bc24ea
-- title:
--   Exists Isometry Of Linear Independent
-- statement:
--   Definitions and structural lemmas for Exists Isometry Of Linear Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfLinearIndependent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.WittTrace
open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt
section Abstract
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
end Abstract
end GlobalTheory.WittTrace


