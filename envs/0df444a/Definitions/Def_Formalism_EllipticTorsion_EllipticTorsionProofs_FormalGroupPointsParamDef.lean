-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:34.561626+00:00
-- url     : https://prove2.me/theorems/c94c44cf-ed2c-4ebf-911c-390f24bc1b5f
-- title:
--   Formal Group Points Param Def
-- statement:
--   Definitions and structural lemmas for Formal Group Points Param Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
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
namespace FormalGroupPointsParam
open Formalism.G
section Eval
variable {K : Type u} [NormedField K]
def AbsSum (f : PowerSeries K) (t : K) : Prop := Summable fun n => ‖coeff n f * t ^ n‖
def Ev (f : PowerSeries K) (t v : K) : Prop := AbsSum f t ∧ evalPS f t = v
variable [CompleteSpace K]
end Eval
section Ultra
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable [CompleteSpace K]
end Ultra
end FormalGroupPointsParam
end Formalism.ELL


