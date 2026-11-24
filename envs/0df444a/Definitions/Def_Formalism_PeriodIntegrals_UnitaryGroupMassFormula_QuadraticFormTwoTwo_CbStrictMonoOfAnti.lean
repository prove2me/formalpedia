-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:28:44.16052+00:00
-- url     : https://prove2.me/theorems/0b8ef065-b950-4c43-82e6-ac982b57ffd8
-- title:
--   Cb Strict Mono Of Anti
-- statement:
--   Definitions and structural lemmas for Cb Strict Mono Of Anti, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def cb_xPoly (Q : M.Par) (σ : M.Ty Q) : Polynomial ℂ :=
  ∏ i ∈ Icc 1 (Q.k - 1), (Polynomial.X + Polynomial.C ((M.rho Q σ i : ℝ) : ℂ))
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors


