-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:23.960005+00:00
-- url     : https://prove2.me/theorems/de07af03-ee99-4c85-8155-49fb495e95b6
-- title:
--   Coeff Pow Eq Zero Of Degree Lt
-- statement:
--   Definitions and structural lemmas for Coeff Pow Eq Zero Of Degree Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffPowEqZeroOfDegreeLt.lean

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.JetsPhW
namespace PI.JetsPhW.Ch
section Chain
variable {R : Type*} [CommRing R] {σ : Type*}
def sumL (l : PowerSeries R) (c : σ → R) (s : Finset σ) : MvPowerSeries σ R :=
  ∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (MvPowerSeries.X j) l
def DvR (v : PowerSeries R) (i : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  PowerSeries.subst (MvPowerSeries.X i) v * MvPowerSeries.pderiv R i f
end Chain
end PI.JetsPhW.Ch


