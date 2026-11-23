-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormRepresentationLift_ExistsMulEqOneAddSmulOfRowsGe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormRepresentationLift_ExistsMulEqOneAddSmulOfRowsGe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:11.051688+00:00
-- url     : https://prove2.me/theorems/041982b1-e50f-4846-9a3e-69e17cca2724
-- title:
--   Exists Mul Eq One Add Smul Of Rows Ge
-- statement:
--   Definitions and structural lemmas for Exists Mul Eq One Add Smul Of Rows Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormRepresentationLift/ExistsMulEqOneAddSmulOfRowsGe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.NRL
open Matrix
variable {R : Type*} [CommRing R] {r : ℕ}
def UniUp (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : Prop :=
  (∀ a b, b < a → ξ a b = 0) ∧ ∀ a, ξ a a = 1
def rowMat (a : Fin (r + 1)) (w : Fin (r + 1) → R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  fun d c => if d = a then w c else 0
end PI.NRL


