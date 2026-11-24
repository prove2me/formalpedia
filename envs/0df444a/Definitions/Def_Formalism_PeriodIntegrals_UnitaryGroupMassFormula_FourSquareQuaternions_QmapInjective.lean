-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QmapInjective
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QmapInjective
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:33:53.681522+00:00
-- url     : https://prove2.me/theorems/6e1ef259-49c9-4caa-ba84-90c6e9322547
-- title:
--   Qmap Injective
-- statement:
--   Definitions and structural lemmas for Qmap Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QmapInjective.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace PI.KerIso.FourSqW
open PI.KerFourSqW
def qmap {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) :
    (Fin 4 → E) →ₗ[K] (Fin 4 × n → K) where
  toFun x w := ∑ a, (Q w.2 w.1 a : K) * b.repr (x a) w.2
  map_add' x y := by
    ext w
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext w
    simp [Finset.mul_sum, mul_left_comm]
end PI.KerIso.FourSqW


