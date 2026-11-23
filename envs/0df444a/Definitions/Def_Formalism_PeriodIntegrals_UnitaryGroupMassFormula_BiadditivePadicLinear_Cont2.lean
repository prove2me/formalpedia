-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_Cont2
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_Cont2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:44.574012+00:00
-- url     : https://prove2.me/theorems/fd1b1b78-a469-44b2-87bd-52791f8f955f
-- title:
--   Cont2
-- statement:
--   Definitions and structural lemmas for Cont2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BiadditivePadicLinear/Cont2.lean

import Definitions.Def_Formalism_PeriodIntegrals_BiaddZpLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.BiaddZpLinW
open PI.BiaddZpLin
def Cont2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.constantCoeff l = 0 →
    (∀ n : ℕ, Simeq (be l ex ph (mulBy l ex (n : ℂ_[p]) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv 0) (Xv 1))) →
    ∀ n : ℤ_[p], Simeq (be l ex ph (mulBy l ex (zc n) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (zc n) * be l ex ph (Xv 0) (Xv 1))
end PI.BiaddZpLinW


