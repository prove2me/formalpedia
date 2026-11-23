-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:22.468988+00:00
-- url     : https://prove2.me/theorems/d065a06f-cc26-4a92-bf02-a5c4c5218b64
-- title:
--   Wp Shape
-- statement:
--   Definitions and structural lemmas for Wp Shape, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
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
namespace WpSh
variable {K : Type u} [Field K]
def ClearedM (g2 g3 : K) (M : K⟦X⟧) : Prop :=
  (X * derivative K M - 2 * M) ^ 2 = 4 * M ^ 3 - C g2 * X ^ 4 * M - C g3 * X ^ 6
def Cleared (g2 g3 : K) (r : K⟦X⟧) : Prop :=
  (-2 + X ^ 3 * derivative K r) ^ 2 =
    4 * (1 + X ^ 2 * r) ^ 3 - C g2 * X ^ 4 * (1 + X ^ 2 * r) - C g3 * X ^ 6
end WpSh
open WpSh
end Formalism.L2.Th1.A


