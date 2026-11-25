-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_AnaSys
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_AnaSys
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T07:08:20.473063+00:00
-- url     : https://prove2.me/theorems/acc1210c-5b87-51f4-b938-c5b81a0cc3c4
-- title:
--   Ana Sys
-- statement:
--   Definitions and structural lemmas for Ana Sys, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/AnaSys.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Bridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_shortInv
import Theorems.Thm_Formalism_L2_Th1_F_discNeZero
import Theorems.Thm_Formalism_L2_Th1_F_sgStarBasic
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
open PowerSeries
noncomputable section
namespace Formalism.L2.Th1.E
namespace AnaSys
open Formalism.L2.Th1
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
def Rd (f : ℂ → ℂ) (S : PowerSeries ℂ_[l]) : Prop := AnalyticAt ℂ f 0 ∧ inU l L ι f = S
variable {l L ι}
variable (l L ι)
theorem analytic_opU (x : ℂ) : AnalyticAt ℂ (F.opU L x (F.sgStar L)) 0 := by
  have h := (F.sgStarBasic L).1
  have : Differentiable ℂ (fun z => F.sgStar L (z + x) *
      Complex.exp (-(Real.pi : ℂ) * (z * (starRingEnd ℂ) x / (F.area L : ℂ))
        - (Real.pi : ℂ) * F.herm L x x / 2)) := by
    fun_prop
  exact this.analyticAt 0
theorem Rd.opU (x : ℂ) :
    Rd l L ι (F.opU L x (F.sgStar L)) (inU l L ι (F.opU L x (F.sgStar L))) :=
  ⟨analytic_opU L x, rfl⟩
theorem disc_ne : (curveL l L ι).Δ ≠ 0 := by
  rw [curveL, (A.shortInv ℂ_[l] _ _).2.2.2]
  intro h
  apply F.discNeZero L
  apply ι.injective
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero]
  exact h
theorem nonsing (t : ℂ) (ht : t ∉ L.lattice) :
    (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (disc_ne l L ι),
    WeierstrassCurve.Affine.equation_iff]
  have h := congrArg ι (L.derivWeierstrassP_sq t ht)
  simp only [map_pow, map_sub, map_mul, map_ofNat] at h
  simp only [curveL, A.shortW]
  linear_combination h / 4
section Trans
open F.TaylorWp
variable (L : PeriodPair) (t : ℂ)
end Trans
end AnaSys
end Formalism.L2.Th1.E


