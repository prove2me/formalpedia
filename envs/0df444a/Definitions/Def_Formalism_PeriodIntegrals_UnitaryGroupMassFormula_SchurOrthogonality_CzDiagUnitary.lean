-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CzDiagUnitary
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CzDiagUnitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:18.108703+00:00
-- url     : https://prove2.me/theorems/d2a526c0-83f0-4965-8450-d9a10a79e552
-- title:
--   Cz Diag Unitary
-- statement:
--   Definitions and structural lemmas for Cz Diag Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CzDiagUnitary.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WSF
open MvPolynomial Matrix
open scoped ComplexOrder
def czFam {N : ℕ} (u v : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin N) ℂ) :
    MvPolynomial (Fin N) ℂ :=
  bind₁ (fun w : Fin N × Fin N => ∑ c : Fin N, C (u w.1 c * v c w.2) * X c) P
end PI.WSF


