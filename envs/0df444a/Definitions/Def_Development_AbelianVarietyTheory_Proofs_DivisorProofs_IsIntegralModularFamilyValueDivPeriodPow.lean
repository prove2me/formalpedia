-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralModularFamilyValueDivPeriodPow
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralModularFamilyValueDivPeriodPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:34.947398+00:00
-- url     : https://prove2.me/theorems/57b002ae-48db-465c-8903-83a9ee446adf
-- title:
--   Is Integral Modular Family Value Div Period Pow
-- statement:
--   Definitions and structural lemmas for Is Integral Modular Family Value Div Period Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralModularFamilyValueDivPeriodPow.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmPowTwelveDivDiscriminantMemSubringStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfEsymmMemSubringStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
namespace GlobalTheory.QFam
end GlobalTheory.QFam


