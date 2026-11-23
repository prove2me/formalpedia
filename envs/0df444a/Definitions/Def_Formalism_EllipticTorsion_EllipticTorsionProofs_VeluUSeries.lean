-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:18.354684+00:00
-- url     : https://prove2.me/theorems/f904bb95-5763-4efe-a77d-966a0a792832
-- title:
--   Velu USeries
-- statement:
--   Definitions and structural lemmas for Velu USeries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluUSeries.lean

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
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
namespace VeluCoordinateMaps
open Formalism.G
section Map
variable {K L : Type*} [Field K] [Field L] (f : K →+* L) (W : WeierstrassCurve K) (a b : K)
end Map
section Ball
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K} (hW : IntegralModel W) {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
include hW ha hb
end Ball
section Terms
variable {F : Type*} [Field F]
end Terms
end VeluCoordinateMaps
end Formalism.ELL


