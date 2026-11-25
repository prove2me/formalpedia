-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:45:14.555257+00:00
-- url     : https://prove2.me/theorems/ac48bb53-ca5c-5b02-828e-44003c83cab6
-- title:
--   Norm Le One Of Monic Two
-- statement:
--   Definitions and structural lemmas for Norm Le One Of Monic Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/NormLeOneOfMonicTwo.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
namespace Formalism.L2.Th1.A
namespace Q2
section Parity
variable {R : Type u} [CommRing R]
variable {K : Type u} [Field K] [CharZero K]
end Parity
section Ball
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Ball
end Q2
open Q2
end Formalism.L2.Th1.A


