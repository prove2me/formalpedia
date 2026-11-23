-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsOne
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_JetsOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:17.979587+00:00
-- url     : https://prove2.me/theorems/36cfca68-4b3c-4393-8eb8-c5b2f144e5f4
-- title:
--   Jets One
-- statement:
--   Definitions and structural lemmas for Jets One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsOne.lean

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
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
namespace Formalism.ELL.FormalGroupLinearJets
variable {K : Type u} [CommRing K]
end Formalism.ELL.FormalGroupLinearJets
namespace Formalism.ELL
open Formalism.G Formalism.ELL.FormalGroupLinearJets
end Formalism.ELL


