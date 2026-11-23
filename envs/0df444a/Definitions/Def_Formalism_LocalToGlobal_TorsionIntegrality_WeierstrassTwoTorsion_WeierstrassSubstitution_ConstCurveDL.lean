-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ConstCurveDL
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ConstCurveDL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:45.680059+00:00
-- url     : https://prove2.me/theorems/bc3319d3-25d0-4cc6-af9d-79c0d2f58bab
-- title:
--   Const Curve DL
-- statement:
--   Definitions and structural lemmas for Const Curve DL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ConstCurveDL.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.L2.Th1.A
namespace Wp
variable {K : Type u} [Field K]
def sig {e : K⟦X⟧} (he : HasSubst e) : K⟦X⟧ →+* LaurentSeries K :=
  toL.comp (substAlgHom he : K⟦X⟧ →ₐ[K] K⟦X⟧).toRingHom
variable (W : WeierstrassCurve K) {e : K⟦X⟧} (he : HasSubst e)
end Wp
open Wp
end Formalism.L2.Th1.A


