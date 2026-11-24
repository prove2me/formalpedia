-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:50.862798+00:00
-- url     : https://prove2.me/theorems/9f712e64-1561-4d21-a87d-db8377d56c80
-- title:
--   Gram Matrix Duality
-- statement:
--   Definitions and structural lemmas for Gram Matrix Duality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/GramMatrixDuality.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV
section Form
variable {σ : Type}
def fqB (c : ℚ) : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun P Q => fockQ P Q / c)
    (fun P P' Q => by rw [we_fock_add_left, add_div])
    (fun a P Q => by rw [smul_eq_mul, we_fock_smul_left, mul_div_assoc])
    (fun P Q Q' => by rw [we_fock_add_right, add_div])
    (fun a P Q => by rw [smul_eq_mul, we_fock_smul_right, mul_div_assoc])
end Form
end PI.SlopeSteps


