-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:47.105438+00:00
-- url     : https://prove2.me/theorems/e9841d28-0035-4d84-80e1-2dfa33fadf84
-- title:
--   Sum Multinomial Sub
-- statement:
--   Definitions and structural lemmas for Sum Multinomial Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean

import Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitaryGroupMassFormula.TayInvPow
open MvPowerSeries
section
variable {σ : Type*} {A : Type*} [CommRing A]
def deg (β : σ →₀ ℕ) : ℕ := β.sum fun _ n => n
def cprod (c : σ →₀ A) (β : σ →₀ ℕ) : A := β.prod fun p b => c p ^ b
def cf (c : σ →₀ A) (t : A) (k : ℕ) (β : σ →₀ ℕ) : A :=
  (-1) ^ deg β * (((k + deg β - 1).choose (deg β) : ℕ) : A) *
    ((Nat.multinomial β.support β : ℕ) : A) * cprod c β * t ^ (k + deg β)
def F (c : σ →₀ A) (t : A) (k : ℕ) : MvPowerSeries σ A := fun β => cf c t k β
end
end PI.UnitaryGroupMassFormula.TayInvPow


