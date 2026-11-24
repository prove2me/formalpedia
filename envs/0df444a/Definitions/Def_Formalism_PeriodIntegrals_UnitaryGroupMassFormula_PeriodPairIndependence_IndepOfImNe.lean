-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PeriodPairIndependence_IndepOfImNe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PeriodPairIndependence_IndepOfImNe
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:52.703039+00:00
-- url     : https://prove2.me/theorems/6b891f98-9ff0-4f38-b823-c17bda77c45c
-- title:
--   Indep Of Im Ne
-- statement:
--   Definitions and structural lemmas for Indep Of Im Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PeriodPairIndependence/IndepOfImNe.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ComplexConjugate
open scoped nonZeroDivisors
namespace PI.KerLat.PerPairProof
def imMul {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (a : ℂ) : K →ₗ[ℚ] ℝ where
  toFun k := (conj a * φ k).im
  map_add' x y := by simp [mul_add]
  map_smul' q x := by
    simp only [Rat.smul_def, map_mul, map_ratCast, RingHom.id_apply]
    rw [mul_left_comm, ← Complex.ofReal_ratCast, Complex.im_ofReal_mul]
end PI.KerLat.PerPairProof


