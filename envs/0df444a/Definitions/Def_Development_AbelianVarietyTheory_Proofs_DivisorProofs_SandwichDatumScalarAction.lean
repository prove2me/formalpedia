-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SandwichDatumScalarAction
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SandwichDatumScalarAction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:30:40.317563+00:00
-- url     : https://prove2.me/theorems/e53813a9-5169-4764-911f-a5d92d4fe5e9
-- title:
--   Sandwich Datum Scalar Action
-- statement:
--   Definitions and structural lemmas for Sandwich Datum Scalar Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SandwichDatumScalarAction.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MuCoeffZeroNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusOfPadic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
namespace GlobalTheory.DetInv.Intertwine
variable {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
end GlobalTheory.DetInv.Intertwine
namespace GlobalTheory.DetInv
end GlobalTheory.DetInv


