-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_DvdPowQSub
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_DvdPowQSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:27.781492+00:00
-- url     : https://prove2.me/theorems/373a96f8-65c1-47dc-8180-6088bd2219ac
-- title:
--   Dvd Pow QSub
-- statement:
--   Definitions and structural lemmas for Dvd Pow QSub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFrob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
noncomputable section
namespace PI.OkpW
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
def tseq (τ : K →+* ℂ_[p]) (a : 𝓞 K) (k : ℕ) : ℂ_[p] := τ ((a ^ ((p ^ 2) ^ k) : 𝓞 K) : K)
def teich (τ : K →+* ℂ_[p]) (a : 𝓞 K) : ℂ_[p] := limUnder atTop (tseq τ a)
end PI.OkpW


