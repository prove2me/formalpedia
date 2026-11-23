-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WfSubst
-- name    : Formalism_PeriodIntegrals_WfSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:13.44314+00:00
-- url     : https://prove2.me/theorems/0c92a558-46a7-44be-94c6-bc384b3e5719
-- title:
--   Wf Subst
-- statement:
--   Definitions and structural lemmas for Wf Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WfSubst.lean

import Definitions.Def_Formalism_PeriodIntegrals_ExpIntW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def SubstSub : Prop :=
  ∀ (A : Type) [CommRing A] (S : Subring A) (σ : Type) (f : PowerSeries A) (a : MvPowerSeries σ A),
    (∀ n, PowerSeries.coeff n f ∈ S) → (∀ n, MvPowerSeries.coeff n a ∈ S) →
    MvPowerSeries.constantCoeff a = 0 → ∀ n, MvPowerSeries.coeff n (PowerSeries.subst a f) ∈ S
def WfSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    CoefWf f → CoefWf a → MvPowerSeries.constantCoeff a = 0 → CoefWf (PowerSeries.subst a f)
end PI


