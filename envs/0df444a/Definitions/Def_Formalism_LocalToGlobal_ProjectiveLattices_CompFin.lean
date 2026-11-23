-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CompFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:44.424846+00:00
-- url     : https://prove2.me/theorems/845fd2ff-cb04-4ad1-8c4e-2028f7118138
-- title:
--   Comp Fin
-- statement:
--   Definitions and structural lemmas for Comp Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompFin.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.CompFin
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
end Formalism.L2.Pj.CompFin


