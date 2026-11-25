-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushL
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushL
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:46.446371+00:00
-- url     : https://prove2.me/theorems/dc3c3fa9-cb67-434a-93d1-6a8168ea1002
-- title:
--   Orbit Push L
-- statement:
--   Definitions and structural lemmas for Orbit Push L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushL.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Theorems.Thm_PI_RhsWLim_W_ofW_toW
import Theorems.Thm_PI_RhsWLim_W_toW_ofW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W
open PI.RhsWLim
def wEquiv (k : ℕ) : ((Fin k → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun := toW k
  invFun := ofW k
  map_add' p q := by
    funext j
    unfold toW
    by_cases h : j.val < k
    · simp only [dif_pos h, Prod.fst_add, Pi.add_apply]
    · simp only [dif_neg h, Prod.snd_add, Pi.add_apply]
  map_smul' c p := by
    funext j
    unfold toW
    by_cases h : j.val < k
    · simp only [dif_pos h, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
    · simp only [dif_neg h, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
  left_inv := ofW_toW
  right_inv := toW_ofW
def blkLin (k : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ((Fin k → ℂ) × ℂ) →ₗ[ℂ] ((Fin k → ℂ) × ℂ) :=
  (((wEquiv k).symm : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] ((Fin k → ℂ) × ℂ)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] ((Fin k → ℂ) × ℂ)) ∘ₗ
    Matrix.toLin' μ ∘ₗ (((wEquiv k).symm.symm : ((Fin k → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ)) :
      ((Fin k → ℂ) × ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ))
end PI.RhsWLim.W


