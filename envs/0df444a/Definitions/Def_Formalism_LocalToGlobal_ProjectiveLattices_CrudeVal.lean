-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:14.672376+00:00
-- url     : https://prove2.me/theorems/826b8c89-d0e8-4e73-89b8-46dc33f206ff
-- title:
--   Crude Val
-- statement:
--   Definitions and structural lemmas for Crude Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeVal.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
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
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
  {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K'] {ι : K →+* K'} {e : ℕ}
end Formalism.L2.Pj.Crude


