-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:41:56.502735+00:00
-- url     : https://prove2.me/theorems/7b4db35e-5bd3-4645-8c00-4b3e72499aa7
-- title:
--   Is Square Mul Infinite
-- statement:
--   Definitions and structural lemmas for Is Square Mul Infinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSquareMulInfinite.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero
namespace GlobalTheory.QuadSymbol
namespace NormIndex
section Field
variable {K : Type} [Field K]
def Nm (d x : K) : Prop := ∃ a b : K, x = a ^ 2 - d * b ^ 2
variable (w : Valuation K ℤᵐ⁰)
end Field
section Completion
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end Completion
end NormIndex
end GlobalTheory.QuadSymbol


