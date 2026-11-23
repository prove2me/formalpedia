-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GenOfTwo
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GenOfTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:09.027974+00:00
-- url     : https://prove2.me/theorems/66c2cbb1-ad76-4b0d-a7bf-8c84b9fab9ae
-- title:
--   Gen Of Two
-- statement:
--   Definitions and structural lemmas for Gen Of Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/GenOfTwo.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_QuadRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace MassDataIdxEmb
open NumberField IsDedekindDomain Polynomial
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end MassDataIdxEmb


