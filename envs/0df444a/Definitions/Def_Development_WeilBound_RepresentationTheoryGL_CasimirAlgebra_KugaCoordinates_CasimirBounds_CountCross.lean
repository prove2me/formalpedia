-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountCross
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountCross
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:07.013486+00:00
-- url     : https://prove2.me/theorems/b3f13c8a-9de6-4a55-ab57-bc3d314224d9
-- title:
--   Count Cross
-- statement:
--   Definitions and structural lemmas for Count Cross, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/CountCross.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountSame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option linter.unusedSectionVars false
namespace PositivityTheory.Rg.Cz
section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}
end
end PositivityTheory.Rg.Cz


