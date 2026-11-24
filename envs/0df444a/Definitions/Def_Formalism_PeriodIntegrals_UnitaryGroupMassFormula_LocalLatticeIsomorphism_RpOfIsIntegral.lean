-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:34.811576+00:00
-- url     : https://prove2.me/theorems/f193a661-8822-4ca6-869b-74c80636637d
-- title:
--   Rp Of Is Integral
-- statement:
--   Definitions and structural lemmas for Rp Of Is Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
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
section
variable {K : Type} [Field K] [NumberField K]
end
section
variable {K : Type} [Field K] {ι : Type} [Fintype ι] (c : K →+* K)
end
section
variable {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type} [Fintype ι]
  {L : Set (ι → K)}
end
end PI.KLW


