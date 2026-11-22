-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PairingPowMemSymbolRange
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PairingPowMemSymbolRange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:44.596618+00:00
-- url     : https://prove2.me/theorems/48b2df7f-b0c3-48e0-b6d3-f519a80b1a7d
-- title:
--   Pairing Pow Mem Symbol Range
-- statement:
--   Definitions and structural lemmas for Pairing Pow Mem Symbol Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PairingPowMemSymbolRange.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
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
variable (K : Type) [Field K] [CharZero K] (k d : ℕ)
def Sc (c : ℕ) : Submodule K (Pol K k) :=
  ((Wc K k d c).map (kappa K k d)).comap (LinearMap.mulLeft K (tt K k ^ (d - c)))
end PI.OpWords


