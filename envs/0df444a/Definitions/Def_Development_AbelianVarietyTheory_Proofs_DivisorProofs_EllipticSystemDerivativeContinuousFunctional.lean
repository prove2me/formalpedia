-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctional
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctional
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:50.784971+00:00
-- url     : https://prove2.me/theorems/be47bd6e-a021-4497-a27f-48726247e933
-- title:
--   Elliptic System Derivative Continuous Functional
-- statement:
--   Definitions and structural lemmas for Elliptic System Derivative Continuous Functional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticSystemDerivativeContinuousFunctional.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDerivStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
namespace GlobalTheory.HCA.SolFunc
variable {d : ℕ}
def extLin {U : Set (E d)} (S : Submodule ℂ (U →ᵇ ℂ)) : S →ₗ[ℂ] (E d → ℂ) where
  toFun u := ext0 U ((u : U →ᵇ ℂ) : U → ℂ)
  map_add' u v := by funext x; exact GlobalTheory.HCA.SolSub.matrixExtendByZero_add (u : U →ᵇ ℂ) v x
  map_smul' c u := by funext x; exact GlobalTheory.HCA.SolSub.extendByZeroOffSubset_smul_apply c (u : U →ᵇ ℂ) x
end GlobalTheory.HCA.SolFunc


