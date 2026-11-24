-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:51.877782+00:00
-- url     : https://prove2.me/theorems/48dff818-7595-4890-9ff7-e16b3fdeaf20
-- title:
--   Mnr Update Eq Zero
-- statement:
--   Definitions and structural lemmas for Mnr Update Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean

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
namespace PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
def mnr (R : Type*) [CommRing R] {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) :
    MvPolynomial (Fin k × Fin k) R :=
  (Matrix.of fun p q : Fin n => (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R)).det
end PI.OddDualWeyl.Low
namespace PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
section Step
variable {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
end Step
end PI.OddDualWeyl.Low
namespace PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
end PI.OddDualWeyl.Low
namespace PI.OddDualWeyl
end PI.OddDualWeyl


