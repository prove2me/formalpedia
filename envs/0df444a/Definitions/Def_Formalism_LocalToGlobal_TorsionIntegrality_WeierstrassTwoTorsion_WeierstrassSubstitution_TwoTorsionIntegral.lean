-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:40.832499+00:00
-- url     : https://prove2.me/theorems/abbef102-2ee0-4a1e-9c2a-eae0f199afa1
-- title:
--   Two Torsion Integral
-- statement:
--   Definitions and structural lemmas for Two Torsion Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
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
universe u
noncomputable section
namespace Formalism.L2.Th1.A
namespace Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
theorem e0 : constantCoeff (expSer W) = 0 := by
  unfold expSer compInv
  split_ifs with h
  · exact h.choose_spec.1
  · simp
theorem he : HasSubst (expSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' (e0 W)
end Two
open Two
namespace Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
end Two
end Formalism.L2.Th1.A


