-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:20.098914+00:00
-- url     : https://prove2.me/theorems/954a9419-09b9-46c8-b05d-013c6957bff6
-- title:
--   Crude Ord
-- statement:
--   Definitions and structural lemmas for Crude Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
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
namespace Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
section Word
variable (Op Op' : PS k n d → PS k n d)
end Word
end Formalism.L2.Pj.Crude


