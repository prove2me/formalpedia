-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralTwConjMemCentMul
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralTwConjMemCentMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:23.071909+00:00
-- url     : https://prove2.me/theorems/d18335ea-1033-4230-a64a-e1224760339b
-- title:
--   Integral Tw Conj Mem Cent Mul
-- statement:
--   Definitions and structural lemmas for Integral Tw Conj Mem Cent Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralTwConjMemCentMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommutantMulIntegralConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitDiscriminantMatrixQuotientIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix
namespace GlobalTheory.TwIntegral
section Basics
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
end Basics
end GlobalTheory.TwIntegral


