-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:05.076671+00:00
-- url     : https://prove2.me/theorems/a4b8c68d-1c97-4a97-a1ef-b4aaa1848797
-- title:
--   Integral Subst Vector
-- statement:
--   Definitions and structural lemmas for Integral Subst Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/IntegralSubstVector.lean

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
namespace Formalism.FG.IntegralSubstitution
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
end Formalism.FG.IntegralSubstitution


