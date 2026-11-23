-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzConstantInverseDifferentEisenstein
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzConstantInverseDifferentEisenstein
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:34.925872+00:00
-- url     : https://prove2.me/theorems/69a14b3a-d4d6-4643-9b1b-8092d8dc96a5
-- title:
--   Lipschitz Constant Inverse Different Eisenstein
-- statement:
--   Definitions and structural lemmas for Lipschitz Constant Inverse Different Eisenstein, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LipschitzConstantInverseDifferentEisenstein.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
namespace GlobalTheory.LipEisConst
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
end GlobalTheory.LipEisConst


