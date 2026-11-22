-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:06.179032+00:00
-- url     : https://prove2.me/theorems/c9e5a32d-beff-4f3f-9836-bd23f263792e
-- title:
--   Kappa Coeff
-- statement:
--   Definitions and structural lemmas for Kappa Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
namespace PI.OpWords
variable {K : Type} [Field K] {k d : ℕ}
end PI.OpWords


