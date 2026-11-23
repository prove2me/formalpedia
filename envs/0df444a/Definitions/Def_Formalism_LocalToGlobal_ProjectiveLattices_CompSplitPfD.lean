-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfD
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:56.243014+00:00
-- url     : https://prove2.me/theorems/42ef1b24-ea16-4472-a893-5bc18d76fd7b
-- title:
--   Comp Split Pf D
-- statement:
--   Definitions and structural lemmas for Comp Split Pf D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfD.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.CompSplitPfD
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
end Formalism.L2.Pj.CompSplitPfD


