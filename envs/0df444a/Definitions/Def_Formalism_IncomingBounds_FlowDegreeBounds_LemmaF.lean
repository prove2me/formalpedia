-- Prove2me | Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaF
-- name    : Formalism_IncomingBounds_FlowDegreeBounds_LemmaF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:04.952645+00:00
-- url     : https://prove2.me/theorems/69485f13-496c-4603-8ca2-be961f9daa12
-- title:
--   Lemma F
-- statement:
--   Definitions and structural lemmas for Lemma F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaF.lean

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
section Helpers
variable {l d : ℕ} [NeZero d]
def altNum (l d : ℕ) (D : ZMod d → ℝ) (s : ZMod d) : ℝ :=
  ∑ r ∈ Finset.range d, (-1 : ℝ) ^ r * ((l : ℝ) ^ (r + 1))⁻¹ * D (s - (r : ZMod d))
end Helpers
end Formalism.IncomingBounds


