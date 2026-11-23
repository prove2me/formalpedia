-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:53.61014+00:00
-- url     : https://prove2.me/theorems/51eb3571-f7b1-4191-a65b-a6112473facc
-- title:
--   Is Open Nsmul Adelic Completion Of Vector Set
-- statement:
--   Definitions and structural lemmas for Is Open Nsmul Adelic Completion Of Vector Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOpenNsmulAdelicCompletionOfVectorSet.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNsmulIntegersMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NsmulIntegralMemNhdsZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
namespace GlobalTheory.AdLat.OpenLat
variable (F : Type) [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}
end GlobalTheory.AdLat.OpenLat


