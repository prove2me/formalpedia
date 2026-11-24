-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticFormIdeleValuesMemNhdsOne
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticFormIdeleValuesMemNhdsOne
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:44:08.911595+00:00
-- url     : https://prove2.me/theorems/14e5802d-6aac-4e28-8842-aadfc081c612
-- title:
--   Quadratic Form Idele Values Mem Nhds One
-- statement:
--   Definitions and structural lemmas for Quadratic Form Idele Values Mem Nhds One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Topology
namespace GlobalTheory.QNorm
namespace NormOpen
variable {F : Type} [Field F] [NumberField F]
end NormOpen
end GlobalTheory.QNorm


