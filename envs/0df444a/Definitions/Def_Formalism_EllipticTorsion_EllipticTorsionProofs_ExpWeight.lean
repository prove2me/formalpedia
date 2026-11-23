-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExpWeight
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_ExpWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:25.381639+00:00
-- url     : https://prove2.me/theorems/93a87d07-6b8f-491e-91d3-bf0406126c07
-- title:
--   Exp Weight
-- statement:
--   Definitions and structural lemmas for Exp Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExpWeight.lean

import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
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
namespace Formalism.ELL.ExponentialCoefficientWeight
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
end Formalism.ELL.ExponentialCoefficientWeight
namespace Formalism.ELL
open Formalism.G
end Formalism.ELL


