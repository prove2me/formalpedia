-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:53.741131+00:00
-- url     : https://prove2.me/theorems/fbbbe95d-3bc9-4f7b-ab72-71d16a7c0540
-- title:
--   Log Weight
-- statement:
--   Definitions and structural lemmas for Log Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
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
namespace Formalism.ELL.LogarithmWeight
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Formalism.ELL.LogarithmWeight
namespace Formalism.ELL
end Formalism.ELL
end


