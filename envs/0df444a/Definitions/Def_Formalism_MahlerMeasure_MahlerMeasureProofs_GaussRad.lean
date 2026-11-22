-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:42:43.195232+00:00
-- url     : https://prove2.me/theorems/0b042ca7-7b3d-451e-8536-0f8372ad9c1f
-- title:
--   Gauss Rad
-- statement:
--   Definitions and structural lemmas for Gauss Rad, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open Finset Polynomial
section
variable {K : Type} [NormedField K]
variable [IsUltrametricDist K]
end
end Formalism.GM


