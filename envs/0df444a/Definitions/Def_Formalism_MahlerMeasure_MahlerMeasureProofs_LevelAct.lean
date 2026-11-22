-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:43.13423+00:00
-- url     : https://prove2.me/theorems/dfbfe9bb-e6a1-44fe-9568-c285b0b7a232
-- title:
--   Level Act
-- statement:
--   Definitions and structural lemmas for Level Act, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
variable {w e}
end
end Formalism.GM


