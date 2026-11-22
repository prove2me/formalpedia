-- Prove2me | Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
-- name    : Formalism_ZetaNonvanishing_MellinSgen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:55:01.088706+00:00
-- url     : https://prove2.me/theorems/85335f00-a72b-4f8e-8421-60822063df82
-- title:
--   Mellin Sgen
-- statement:
--   Definitions and structural lemmas for Mellin Sgen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section
namespace Formalism
section
variable (a : ℕ → ℝ)
end
end Formalism


