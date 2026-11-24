-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:37.559954+00:00
-- url     : https://prove2.me/theorems/eb259f96-3191-4d9f-9817-ea0b890e75aa
-- title:
--   Rev Col One Transpose
-- statement:
--   Definitions and structural lemmas for Rev Col One Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean

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
namespace PI.OddDualWeyl
section Lin
variable {R : Type} [CommRing R] {k M : ℕ}
theorem rowDiv_add (a b : Fin k) (j : ℕ) (f g : MvPolynomial (Fin k × Fin k) R) :
    rowDiv R a b j (f + g) = rowDiv R a b j f + rowDiv R a b j g := by
  simp only [rowDiv, map_add, Polynomial.coeff_add]
theorem rowDiv_smul (a b : Fin k) (j : ℕ) (c : R) (f : MvPolynomial (Fin k × Fin k) R) :
    rowDiv R a b j (c • f) = c • rowDiv R a b j f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]
def rowDivL (a b : Fin k) (j : ℕ) : MvPolynomial (Fin k × Fin k) R →ₗ[R] MvPolynomial (Fin k × Fin k) R where
  toFun := rowDiv R a b j
  map_add' := rowDiv_add a b j
  map_smul' := rowDiv_smul a b j
end Lin
section Top
variable {K : Type} [Field K]
end Top
end PI.OddDualWeyl


