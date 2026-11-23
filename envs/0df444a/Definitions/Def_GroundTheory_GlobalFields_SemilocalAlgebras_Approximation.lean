-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
-- name    : GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:10.923661+00:00
-- url     : https://prove2.me/theorems/8020b43b-6f1e-4b00-84b4-97cc0cd8df02
-- title:
--   Approximation
-- statement:
--   Definitions and structural lemmas for Approximation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Approximation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter
noncomputable section
namespace SemiLocal
variable {L : Type*} [Field L] [NumberField L]
end SemiLocal
end
end GroundTheory.Global


