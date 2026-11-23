-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaExistence_NormHfLe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaExistence_NormHfLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:06.938168+00:00
-- url     : https://prove2.me/theorems/dc413d63-69c2-4d20-a722-3d9fe8b98b05
-- title:
--   Norm Hf Le
-- statement:
--   Definitions and structural lemmas for Norm Hf Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaExistence/NormHfLe.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaExistence_TermBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.ThGW
namespace Hol
variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]
lemma hf_add_left (A : ℝ) (z z' w : T → I → J → ℂ) :
    HfG A (z + z') w = HfG A z w + HfG A z' w := by
  simp only [HfG, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]
lemma hf_smul_left (A : ℝ) (c : ℂ) (z w : T → I → J → ℂ) :
    HfG A (c • z) w = c * HfG A z w := by
  simp only [HfG, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]
noncomputable def hl (A : ℝ) (v : T → I → J → ℂ) : (T → I → J → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => HfG A z v
      map_add' := fun z z' => hf_add_left A z z' v
      map_smul' := fun c z => by simp only [hf_smul_left, smul_eq_mul, RingHom.id_apply] }
end Hol
end PI.ThGW


