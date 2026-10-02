-- Prove2me | Definitions.Def_ChapterThermalTemperatureCore
-- name    : ChapterThermalTemperatureCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:02:50.659431+00:00
-- url     : https://prove2.me/theorems/802c20f6-a912-4ad4-96bd-8c88d2fd631e
-- title:
--   Chapter ThermalTemperatureCore
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterThermalTemperatureCore.lean`): generated def bundle for ChapterThermalTemperatureCore. See BookProof/ChapterThermalTemperatureCore.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterThermalTemperatureCore.lean

import Definitions.Def_ChapterBoseEinstein
import Mathlib


/-!
# Chapter "The Coherent State of Attention", §"Temperature and the Thermal Bath" —
the finite algebraic core of the temperature identity (plan Part F.4 / A.4)

`ChapterCoherentTemperature` introduces the thermal occupation law through its
*mean* occupation `n̄` and defines the chapter's temperature as `τ = n̄ + 1/2`;
`ChapterBoseEinstein` re-parametrizes the same law by the physical inverse
temperature `x = ħω/kT` and derives the closed form `τ(x) = ½·coth(x/2)`.

This module supplies the **finite algebraic core** that Part A.4 of the plan
flagged as a gap: the geometric occupation law written directly in terms of its
*ratio* `r` (rather than its mean), its first two moments, the zero-point floor
that the extra `½` measures, and the headline that the Bose–Einstein closed form
`½·coth(x/2)` **is** the mean occupation plus one half — i.e. `τ = n̄ + ½` read
off the physical parametrization rather than posited.

## Deliverables

* `geometricOccupancy r n = (1 - r)·rⁿ` — the geometric (thermal) occupation law
  in ratio parametrization, and `geometricOccupancy_eq_thermalProb` identifying
  it with `ChapterCoherentTemperature.thermalProb` at mean `n̄ = r/(1-r)`;
* `geometricOccupancy_tsum_one` — it is a probability law on `ℕ`;
* `geometricOccupancy_mean` — its mean occupation is `r/(1-r)`;
* `geometricOccupancy_variance` — its variance is `r/(1-r)²`, equivalently
  `n̄ + n̄²` at `n̄ = r/(1-r)`;
* `half_integer_floor` — the harmonic-oscillator energy expectation
  `Σₙ (n + ½)·Pr(n)` of the thermal law is `≥ ½`, with equality exactly at the
  vacuum `n̄ = 0`: the extra `½` is a floor no thermal state can go below;
* `thermal_temperature_eq_mean_half` — **headline**: for every `x > 0`,
  `½·coth(x/2) = (Σₙ n·Pr(n)) + ½`, so the physically parametrized temperature
  is the mean occupation plus the zero-point half;
* `thermal_temperature_eq_energy_expectation_coth` — the same closed form read as
  the expectation of the energy observable `n + ½`.

**Recorded disparity with the informal chapter (unchanged).**  The derivation of
`τ` from the quantum *fidelity* of displaced thermal states on Fock space remains
outside this toolchain; what is proved here is the statistical/algebraic identity
`½·coth(x/2) = n̄(x) + ½` together with the moment structure it rests on.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterThermalTemperatureCore

open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

/-! ## The geometric occupation law in ratio parametrization -/

/-- The **geometric (thermal) occupation law** written through its ratio:
`Pr(n) = (1 - r)·rⁿ`.  For `r = n̄/(n̄+1)` this is
`ChapterCoherentTemperature.thermalProb`. -/
def geometricOccupancy (r : ℝ) (n : ℕ) : ℝ := (1 - r) * r ^ n

variable {r : ℝ}



/-- The mean of the ratio-`r` geometric law, `n̄ = r/(1-r)`. -/
def geometricMean (r : ℝ) : ℝ := r / (1 - r)













/-! ## The zero-point floor -/





/-! ## The headline: the closed form is the mean plus a half -/





end BookProof.ChapterThermalTemperatureCore

end


