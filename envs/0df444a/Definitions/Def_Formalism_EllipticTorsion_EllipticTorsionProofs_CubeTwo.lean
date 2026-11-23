-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:12.593352+00:00
-- url     : https://prove2.me/theorems/92861517-cfb4-4d84-8894-4faf396f53dc
-- title:
--   Cube Two
-- statement:
--   Definitions and structural lemmas for Cube Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeTwo.lean

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
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
namespace Formalism.ELL
namespace CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {w : PowerSeries K}
def dI (W : WeierstrassCurve K) (w : PowerSeries K) (i : Fin 2) : MvPowerSeries (Fin 2) K :=
  -1 + ca W.a₁ * MvPowerSeries.X i + ca W.a₃ * Wi w i
end CubeTwoAlt
end Formalism.ELL
namespace Formalism.ELL
namespace CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K] {W : WeierstrassCurve K} {w : PowerSeries K}
local notation "cc" => MvPowerSeries.constantCoeff
end CubeTwoAlt
end Formalism.ELL


