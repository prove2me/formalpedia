-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharProd
-- name    : Formalism_LocalToGlobal_UnitaryNorms_CharProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:25.886122+00:00
-- url     : https://prove2.me/theorems/d38435ad-11b9-4004-b2ef-293f1f986014
-- title:
--   Char Prod
-- statement:
--   Definitions and structural lemmas for Char Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharProd.lean

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HeckeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace Formalism.L2.Host.HChar
variable {L : Type} [Field L] [NumberField L] (χ : HChar L)
end Formalism.L2.Host.HChar


