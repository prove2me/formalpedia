-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Deuring
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_Deuring
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:30.672278+00:00
-- url     : https://prove2.me/theorems/787ecc8d-4bab-4227-89ab-dc0f356e6243
-- title:
--   Deuring
-- statement:
--   Definitions and structural lemmas for Deuring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Deuring.lean

import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.ELL
namespace DeuringModel
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
end DeuringModel
end Formalism.ELL


