-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeSumEqConeSum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeSumEqConeSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:59.144894+00:00
-- url     : https://prove2.me/theorems/ba0d765d-a09c-47c1-86f6-b6155bf12cd2
-- title:
--   Lattice Sum Eq Cone Sum
-- statement:
--   Definitions and structural lemmas for Lattice Sum Eq Cone Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeSumEqConeSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemTraceDualSignedPositiveConeIffTotallyPositiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzConstantInverseDifferentEisensteinStatement
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
noncomputable section
namespace GlobalTheory.EisPerB
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.EisPerB


