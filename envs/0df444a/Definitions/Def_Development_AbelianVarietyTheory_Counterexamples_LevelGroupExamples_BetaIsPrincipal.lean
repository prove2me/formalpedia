-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
-- name    : Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:59:40.358113+00:00
-- url     : https://prove2.me/theorems/80dede89-e84a-4275-96ba-7f0ae04fd50b
-- title:
--   Beta Is Principal
-- statement:
--   Definitions and structural lemmas for Beta Is Principal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/BetaIsPrincipal.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaCounterexample
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)
end GlobalTheory.BetaCounterexample


