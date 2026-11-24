-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemIntegralClosureIffMemBall
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemIntegralClosureIffMemBall
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:03.200234+00:00
-- url     : https://prove2.me/theorems/47ec988a-1db4-44a9-986c-c0477cb7c503
-- title:
--   Mem Integral Closure Iff Mem Ball
-- statement:
--   Definitions and structural lemmas for Mem Integral Closure Iff Mem Ball, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/MemIntegralClosureIffMemBall.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
namespace PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
variable {l : ℕ} [hl : Fact l.Prime]
theorem algebraMap_padicInt_injective (K : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥K.1) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥K.1]
  exact (algebraMap ℚ_[l] ↥K.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
instance isTorsionFree_finExt (K : FinExt l) : Module.IsTorsionFree ℤ_[l] ↥K.1 where
  isSMulRegular r hr := fun x y h => by
    have hr0 : algebraMap ℤ_[l] ↥K.1 r ≠ 0 := by
      intro h0
      exact hr.ne_zero ((map_eq_zero_iff _ (algebraMap_padicInt_injective K)).1 h0)
    change r • x = r • y at h
    simp only [Algebra.smul_def] at h
    exact mul_left_cancel₀ hr0 h
end PI.CompDegEF


