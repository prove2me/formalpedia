-- Prove2me | Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Window
-- name    : Formalism_ResultantValuation_ResultantAdjugateProofs_Window
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:08.412137+00:00
-- url     : https://prove2.me/theorems/a9d3a1d8-ce20-472a-9bdd-8bb33f015b98
-- title:
--   Window
-- statement:
--   Definitions and structural lemmas for Window, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Window.lean

import Mathlib
import Definitions.Def_Formalism_ResultantValuation_WindowValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.ResultantValuation
section Padic
variable {l : ℕ} [Fact l.Prime]
end Padic
end Formalism.ResultantValuation


