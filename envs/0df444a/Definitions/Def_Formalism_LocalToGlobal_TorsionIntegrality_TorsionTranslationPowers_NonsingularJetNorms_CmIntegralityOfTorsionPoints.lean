-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_CmIntegralityOfTorsionPoints
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_CmIntegralityOfTorsionPoints
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:22:49.939171+00:00
-- url     : https://prove2.me/theorems/fb16470f-c2f8-47f2-aed8-123a229e7ebe
-- title:
--   Cm Integrality Of Torsion Points
-- statement:
--   Definitions and structural lemmas for Cm Integrality Of Torsion Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
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
namespace Formalism.L2.Th1.E
namespace ScaledModelNorms
open Formalism.L2.Th1
variable (l : ℕ) [Fact l.Prime]
variable (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
theorem nonsing (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, WeierstrassCurve.Affine.equation_iff]
  have h := congrArg ι (PeriodPair.derivWeierstrassP_sq L t ht)
  simp only [map_sub, map_mul, map_pow, map_ofNat] at h
  show (ι (L.derivWeierstrassP t) / 2) ^ 2 + 0 * ι (L.weierstrassP t) * (ι (L.derivWeierstrassP t) / 2) +
      0 * (ι (L.derivWeierstrassP t) / 2) =
    ι (L.weierstrassP t) ^ 3 + 0 * ι (L.weierstrassP t) ^ 2 + (-ι L.g₂ / 4) * ι (L.weierstrassP t) +
      (-ι L.g₃ / 4)
  linear_combination (1 / 4 : ℂ_[l]) * h
end ScaledModelNorms
end Formalism.L2.Th1.E


