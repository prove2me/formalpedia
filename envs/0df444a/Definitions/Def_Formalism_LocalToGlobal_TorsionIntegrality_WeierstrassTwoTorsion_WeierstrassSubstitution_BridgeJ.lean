-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:18.265494+00:00
-- url     : https://prove2.me/theorems/ecb9508e-098f-480d-a154-904a5b48507f
-- title:
--   Bridge J
-- statement:
--   Definitions and structural lemmas for Bridge J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeJ.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
namespace Formalism.L2.Th1.A
namespace Bridge
section Ball
variable {K : Type} [NormedField K] [IsUltrametricDist K]
def model (W : WeierstrassCurve K) (h : IntModel W) : WeierstrassCurve (Formalism.G.unitBall K) :=
  ⟨⟨W.a₁, h.1⟩, ⟨W.a₂, h.2.1⟩, ⟨W.a₃, h.2.2.1⟩, ⟨W.a₄, h.2.2.2.1⟩, ⟨W.a₆, h.2.2.2.2⟩⟩
end Ball
end Bridge
open Bridge
end Formalism.L2.Th1.A


