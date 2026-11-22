-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:49:02.711242+00:00
-- url     : https://prove2.me/theorems/5d49405c-3a82-40e1-947f-dc1a8f43fdbb
-- title:
--   Lie Mat
-- statement:
--   Definitions and structural lemmas for Lie Mat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.DetBound
open Finset Polynomial
section Gauss
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Gauss
end Formalism.GM.DetBound
namespace Formalism.GM
open Finset Polynomial DetBound
end Formalism.GM


