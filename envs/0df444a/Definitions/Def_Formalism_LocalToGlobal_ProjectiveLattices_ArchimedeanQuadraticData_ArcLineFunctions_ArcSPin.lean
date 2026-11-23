-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ArcLineFunctions_ArcSPin
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ArcLineFunctions_ArcSPin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:25.370821+00:00
-- url     : https://prove2.me/theorems/d0c63639-c3e5-4f79-af06-8154fdb0e33a
-- title:
--   Arc SPin
-- statement:
--   Definitions and structural lemmas for Arc SPin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/ArcLineFunctions/ArcSPin.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.QAt
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
end Formalism.L2.Pj.QAt


