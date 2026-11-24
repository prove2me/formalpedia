-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairingFactorsThroughPeriods
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairingFactorsThroughPeriods
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:12.441406+00:00
-- url     : https://prove2.me/theorems/4dfdac32-798d-428d-894f-909bc0b86546
-- title:
--   Pairing Factors Through Periods
-- statement:
--   Definitions and structural lemmas for Pairing Factors Through Periods, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairingFactorsThroughPeriods.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace PI.KLW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) {n : Type} [Fintype n]
  (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (p : ℕ)
  (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K))
end PI.KLW


