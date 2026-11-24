-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:39.358803+00:00
-- url     : https://prove2.me/theorems/0b7f9f66-d21b-4a5f-ac5c-c8b93daa7158
-- title:
--   Aeval Mul Homog
-- statement:
--   Definitions and structural lemmas for Aeval Mul Homog, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
def sbs (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) :
    MvPolynomial (Fin k × Fin k) R →ₐ[R] MvPolynomial (Fin k × Fin k) R :=
  aeval fun v => A v.1 v.2
def cM (g : Matrix (Fin k) (Fin k) R) : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R) :=
  g.map C
section Field
variable {K : Type*} [Field K] {k : ℕ}
end Field
end PI.OddDualWeyl.Red
namespace PI.OddDualWeyl
open Red
end PI.OddDualWeyl


