-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_InfinitePadicComplex
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_InfinitePadicComplex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:38.218453+00:00
-- url     : https://prove2.me/theorems/68f1f6bc-42c4-4cc4-a850-8b8b554f066a
-- title:
--   Infinite Padic Complex
-- statement:
--   Definitions and structural lemmas for Infinite Padic Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/InfinitePadicComplex.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
namespace PI.WwMainW
open PI.WwMain PI.WwMain.KM
instance infinitePadicComplex (l : ℕ) [Fact l.Prime] : Infinite ℂ_[l] :=
  Infinite.of_injective (Nat.cast : ℕ → ℂ_[l]) Nat.cast_injective
end PI.WwMainW


