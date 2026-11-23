-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_EpNontrivial
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_EpNontrivial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:21:12.739356+00:00
-- url     : https://prove2.me/theorems/e5bc9736-f435-462e-85f3-6a1020e4690b
-- title:
--   Ep Nontrivial
-- statement:
--   Definitions and structural lemmas for Ep Nontrivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/EpNontrivial.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc Polynomial
namespace PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
end PI.LocLatEq.W


