-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffInnovationPointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:46:43.774539+00:00
-- url     : https://prove2.me/submissions/e713f2b3-f3bf-4e98-b942-906bdb61cd52

import Mathlib.Data.Real.Basic
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalityInnovation
import Definitions.Def_actuarial_finiteReserveYearInnovation
import Definitions.Def_actuarial_finiteLifeDeathIndicator
import Definitions.Def_actuarial_finiteLifeInForceIndicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (K : Ω → ℕ) (t : ℕ) (ω : Ω) :
    finiteReserveYearInnovation (K ω) t (finiteMortalityDeathRate w K) =
      finiteMortalityInnovation w K t ω := by
  rfl
