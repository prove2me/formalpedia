-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:34.725121+00:00
-- url     : https://prove2.me/theorems/74bfdc52-b107-4b07-93b6-8fa0e6c1d3f2
-- title:
--   Capelli Eqv
-- statement:
--   Definitions and structural lemmas for Capelli Eqv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliEqv.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
def lmapPoly {σ τ : Type} (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) (p : Polynomial (MvPolynomial σ ℂ)) :
    Polynomial (MvPolynomial τ ℂ) :=
  ∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.C (φ (p.coeff k)) * Polynomial.X ^ k
end PI.WGL


