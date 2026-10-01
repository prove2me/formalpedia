-- Prove2me | Definitions.Def_ChapterCoherentOccupation
-- name    : ChapterCoherentOccupation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:56:29.056987+00:00
-- url     : https://prove2.me/theorems/22363478-5727-4243-ac8d-e4fc9eff1f9b
-- title:
--   Chapter CoherentOccupation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCoherentOccupation.lean`): generated def bundle for ChapterCoherentOccupation. See BookProof/ChapterCoherentOccupation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCoherentOccupation.lean

import Definitions.Def_ChapterCoherentTemperature
import Mathlib


/-!
# Chapter "The Coherent State of Attention", §"Temperature and the Thermal Bath" —
the occupation statistics of a coherent state

`BookProof/ChapterCoherentTemperature.lean` proves the moment structure of the
*thermal* (Bose–Einstein) occupation distribution and records the temperature
`τ = n̄ + 1/2` as a definition, with the physical derivation flagged as a gap.
Its docstring appeals twice to the *coherent* (Poisson) occupation statistics —
"the Poissonian variance `n̄` of a coherent state" and "the zero-point half".
This module proves those two statements.

What is proved:

* `coherentOccupation` — the coherent-state occupation law
  `p(n) = e^{-λ} λⁿ / n!`, i.e. Mathlib's Poisson probability mass function
  (`coherentOccupation_eq_poissonPMFReal` records the identification);
* `coherentOccupation_hasSum_one`, `coherentOccupation_tsum_one`,
  `coherentOccupation_nonneg` — it is a probability distribution on `ℕ`;
* `coherentOccupation_mean` — its mean occupation is `λ`;
* `coherentOccupation_second_moment` — its second moment is `λ² + λ`;
* `coherentOccupation_variance` — hence its variance is exactly `λ`: coherent
  light is **Poissonian**, the statement `ChapterCoherentTemperature` appeals to;
* `coherentOccupation_energy` — the mean of the harmonic-oscillator energy
  observable `n + 1/2` in a coherent state is `λ + 1/2`, the "mean occupation
  plus the zero-point half";
* `thermalOccupation_energy` and `thermalTemperature_eq_energy_expectation` — the
  same energy identity for the thermal law: the chapter's temperature
  `τ = n̄ + 1/2` **is** the expectation of `n + 1/2` in the thermal state (this
  upgrades `thermalTemperature_eq_mean_add_half` from a restatement of the
  definition to an identity for a genuine observable);
* `coherent_variance_lt_thermal_variance` — for a nonvacuum bath the coherent
  (Poisson) noise `n̄` is strictly below the thermal noise `n̄² + n̄`.

**Recorded disparity with the informal chapter (unchanged).**  What remains a
documented gap is the *physical* derivation of `τ = n̄ + 1/2` from the quantum
fidelity of displaced thermal states on a bosonic Fock space; the identity is
proved here only for the occupation statistics, i.e. as the expectation of the
number-plus-zero-point observable, not from fidelity.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterCoherentOccupation

open Real Nat ProbabilityTheory

/-! ## The exponential series -/



/-! ## The coherent (Poisson) occupation distribution -/

/-- The **occupation distribution of a coherent state** with mean occupation
`λ = |α|²`: the Poisson law `p(n) = e^{-λ} λⁿ / n!`. -/
def coherentOccupation (lam : ℝ) (n : ℕ) : ℝ := Real.exp (-lam) * lam ^ n / n !











/-! ## Moments -/

















/-! ## The thermal law: the temperature is the energy expectation -/

open BookProof.ChapterCoherentTemperature











end BookProof.ChapterCoherentOccupation

end


