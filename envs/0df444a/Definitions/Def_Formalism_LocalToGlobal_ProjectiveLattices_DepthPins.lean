-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DepthPins
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_DepthPins
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:46.630431+00:00
-- url     : https://prove2.me/theorems/7c83b79b-1e39-4ec2-a4cd-978063fda0f8
-- title:
--   Depth Pins
-- statement:
--   Definitions and structural lemmas for Depth Pins, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DepthPins.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def PiHalf (l : Level H) (D : DepData E) : Prop := Ideal.span {D.pi 0 * D.pi 1} = l.Mb
end Formalism.L2.Pj


