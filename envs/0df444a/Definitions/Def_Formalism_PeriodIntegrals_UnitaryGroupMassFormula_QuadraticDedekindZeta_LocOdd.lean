-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_LocOdd
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_LocOdd
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:44.355418+00:00
-- url     : https://prove2.me/theorems/1423475d-a832-40df-8c40-c83fd7e9d706
-- title:
--   Loc Odd
-- statement:
--   Definitions and structural lemmas for Loc Odd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/LocOdd.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ClassNumImQInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible
import Theorems.Thm_imag_quadratic_integral_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace PI.ClassNumImQ.ZetaNonvanishing₂.Loc
variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}
noncomputable def om (hq : QuadData d K b) : 𝓞 K :=
  ⟨(1 + b) / 2, (imag_quadratic_integral_basis d K b hq).1⟩
noncomputable def bb (hq : QuadData d K b) : 𝓞 K := 2 * om hq - 1
end PI.ClassNumImQ.ZetaNonvanishing₂.Loc


