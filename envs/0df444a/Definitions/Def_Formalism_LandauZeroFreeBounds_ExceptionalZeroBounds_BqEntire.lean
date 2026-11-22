-- Prove2me | Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqEntire
-- name    : Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqEntire
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:30.456805+00:00
-- url     : https://prove2.me/theorems/6a54e092-f312-452f-87a2-4777f0055529
-- title:
--   Bq Entire
-- statement:
--   Definitions and structural lemmas for Bq Entire, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqEntire.lean

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
namespace Formalism.ZeroFreeDirichlet
def zetaSubPole : ℂ → ℂ :=
  Function.update (fun s : ℂ => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)
end Formalism.ZeroFreeDirichlet


