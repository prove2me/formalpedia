-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T11:26:59.399231+00:00
-- url     : https://prove2.me/theorems/f2f6162b-c19a-4cfa-aa97-519d1ad0c488
-- title:
--   Integer Endomorphism Instance
-- statement:
--   Definitions and structural lemmas for Integer Endomorphism Instance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IntegerEndomorphismInstance.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_taylor_deriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
namespace Formalism.L2.Th1.F
namespace EndoZ
open PowerSeries TaylorWp
theorem T.deriv {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) :
    T (deriv f) (derivative ℂ F) :=
  ⟨hf.1.deriv, by rw [taylor_deriv.1 f hf.1, hf.2]⟩
theorem T.rescale {f : ℂ → ℂ} {F : PowerSeries ℂ} (a : ℂ) (hf : T f F) :
    T (fun z => f (a * z)) (rescale a F) := by
  refine ⟨?_, by rw [taylor_deriv.2.1 f a hf.1, hf.2]⟩
  exact hf.1.comp_of_eq (analyticAt_const.mul analyticAt_id) (by simp)
def U (L : PeriodPair) (P : ℂ) : Set ℂ :=
  {w | w ∉ L.lattice ∧ w + P ∉ L.lattice ∧ w - P ∉ L.lattice}
def fP (L : PeriodPair) (P : ℂ) (z : ℂ) : ℂ :=
  1 + z ^ 2 * (L.weierstrassPExcept 0 z - L.weierstrassP P)
def mP (L : PeriodPair) (P : ℂ) (z : ℂ) : ℂ :=
  2 * z⁻¹ + wZeta L (z + P) + wZeta L (z - P) - 2 * wZeta L z
end EndoZ
end Formalism.L2.Th1.F


