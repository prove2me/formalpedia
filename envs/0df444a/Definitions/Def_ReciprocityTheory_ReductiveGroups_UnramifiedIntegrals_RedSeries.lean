-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSeries
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSeries
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T07:37:11.509325+00:00
-- url     : https://prove2.me/theorems/69b16360-19b2-5c63-bf35-9c4537852539
-- title:
--   Red Series
-- statement:
--   Definitions and structural lemmas for Red Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSeries.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_mul
import Theorems.Thm_Formalism_L2_Th1_F_taylorDeriv
import Theorems.Thm_Formalism_L2_Th1_F_taylorRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply


set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
namespace ReciprocityTheory.ChartRestriction.L1
def HasT (f : ℂ → ℂ) (s : PowerSeries ℂ) : Prop := AnalyticAt ℂ f 0 ∧ taylor0 f = s
theorem HasT.mul {f g : ℂ → ℂ} {s t : PowerSeries ℂ} (hf : HasT f s) (hg : HasT g t) :
    HasT (fun z => f z * g z) (s * t) :=
  ⟨hf.1.mul hg.1, by rw [(taylorRing.1 f g hf.1 hg.1).2, hf.2, hg.2]⟩
theorem HasT.rescale {f : ℂ → ℂ} {s : PowerSeries ℂ} (hf : HasT f s) (a : ℂ) :
    HasT (fun z => f (a * z)) (PowerSeries.rescale a s) := by
  refine ⟨?_, by rw [taylorDeriv.2.1 f a hf.1, hf.2]⟩
  refine AnalyticAt.fun_comp (f := fun z : ℂ => a * z) (g := f) ?_ (analyticAt_const.mul analyticAt_id)
  simpa using hf.1
def uFun (L : PeriodPair) (z : ℂ) : ℂ := 1 + z ^ 2 * L.weierstrassPExcept 0 z
def homF (u : ℂ → ℂ) (m : ℕ) (Q : ℂ[X]) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (m + 1), Q.coeff i * u z ^ i * z ^ (2 * (m - i))
end ReciprocityTheory.ChartRestriction.L1


