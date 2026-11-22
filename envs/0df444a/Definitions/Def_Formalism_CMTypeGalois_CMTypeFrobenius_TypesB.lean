-- Prove2me | Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB
-- name    : Formalism_CMTypeGalois_CMTypeFrobenius_TypesB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:09.331446+00:00
-- url     : https://prove2.me/theorems/21e4f6ea-4ea3-442e-bd9d-251c34c75e98
-- title:
--   Types B
-- statement:
--   Definitions and structural lemmas for Types B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesB.lean

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace Formalism.Q3
namespace TypesB
variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}
def ext (c : G) (H S : Finset G) : Finset G := S ∪ (H \ S).image (fun x => c * x)
end TypesB
end Formalism.Q3


