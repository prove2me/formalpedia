-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInvTDen
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInvTDen
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:54:50.434914+00:00
-- url     : https://prove2.me/theorems/0f86b0cc-70dc-5068-89cc-43eb2734ced5
-- title:
--   Constant Coeff Inv TDen
-- statement:
--   Definitions and structural lemmas for Constant Coeff Inv TDen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ConstantCoeffInvTDen.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SeriesSubgroup
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
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
open PowerSeries
noncomputable section
namespace Formalism.L2.Th1.E
namespace Shape
def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {a | ‖a‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    change ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha
section Alg
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)
end Alg
section Pts
variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
end Pts
section Nrm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Nrm
end Shape
open Shape
end Formalism.L2.Th1.E


