-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicComplete
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicComplete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:43.775867+00:00
-- url     : https://prove2.me/theorems/4302294e-155d-47f1-98c7-f48915921208
-- title:
--   Subgroup Pow Rel Index Units Of Is Adic Complete
-- statement:
--   Definitions and structural lemmas for Subgroup Pow Rel Index Units Of Is Adic Complete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowRelIndexUnitsOfIsAdicComplete.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowImageUnitsCongruentOneModOfIsAdicCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexOneUnitsMulEqCardQuotientStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
namespace GlobalTheory.CNorm
end GlobalTheory.CNorm


