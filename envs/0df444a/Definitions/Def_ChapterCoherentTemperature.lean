-- Prove2me | Definitions.Def_ChapterCoherentTemperature
-- name    : ChapterCoherentTemperature
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:32:32.730466+00:00
-- url     : https://prove2.me/theorems/4a08e7d3-bc42-44e3-b714-49fb9060c56e
-- title:
--   Chapter CoherentTemperature
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCoherentTemperature.lean`): generated def bundle for ChapterCoherentTemperature. See BookProof/ChapterCoherentTemperature.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCoherentTemperature.lean

import Mathlib


/-!
# Chapter "The Coherent State of Attention", §"Temperature and the Thermal Bath" —
the provable finite core

The chapter claims the temperature identity `τ = n̄ + 1/2` for a displaced thermal
state with mean occupation `n̄`, the `1/2` being the zero-point energy of the
vacuum.

**Status of the full claim: documented gap, not a theorem.**  Deriving
`τ = n̄ + 1/2` requires the quantum fidelity of two *displaced thermal states* on
an infinite-dimensional bosonic Fock space, which is well outside Mathlib
v4.28.0.  Nothing here is `sorry`-ed: instead this module proves the *statistical
core* the identity rests on — the moment structure of the thermal (Bose–Einstein
/ geometric) occupation distribution — and records the remaining step honestly.

What is proved:

* `thermalProb` — the thermal occupation distribution
  `Pr(n) = (1/(n̄+1)) · (n̄/(n̄+1))ⁿ`, i.e. `Pr(n) ∝ (n̄/(n̄+1))ⁿ`;
* `thermalProb_nonneg`, `thermalProb_tsum_one` — it is a probability distribution
  on `ℕ`;
* `thermalProb_mean` — its mean occupation is `n̄`, which is what makes the
  parameter `n̄` deserve its name;
* `thermalProb_second_moment` — its second moment is `2n̄² + n̄`;
* `thermalProb_variance` — hence its variance is `n̄² + n̄`, strictly larger than
  the Poissonian variance `n̄` of a coherent state: the thermal bath adds noise;
* `thermalTemperature` and `thermalTemperature_eq_mean_add_half` — the chapter's
  temperature is the mean occupation plus the zero-point half;
* `thermalTemperature_vacuum` — at `n̄ = 0` (no thermal bosons) the temperature is
  the pure Heisenberg floor `1/2`, matching the factor `2` in the exponent of the
  Softmax derived in `ChapterSoftmaxBorn` (`τ = 1/2`);
* `thermalTemperature_strictMono`, `half_lt_thermalTemperature` — heating the bath
  strictly raises the temperature above that floor.

**Recorded disparity with the informal chapter.**  `thermalTemperature` is a
*definition* (`n̄ ↦ n̄ + 1/2`), not a derived quantity: the physical derivation of
`τ = n̄ + 1/2` from the fidelity of displaced thermal states is the documented gap.
What is a theorem here is that the `n̄` appearing in it is genuinely the mean of
the thermal occupation distribution, and that the distribution's excess variance
over the coherent (Poisson) case is `n̄²`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterCoherentTemperature

/-- The thermal ratio `r = n̄/(n̄+1)` of the Bose–Einstein occupation
distribution. -/
def thermalRatio (nbar : ℝ) : ℝ := nbar / (nbar + 1)

/-- The **thermal occupation distribution** of a bosonic mode with mean
occupation `n̄`: the geometric law `Pr(n) = (1/(n̄+1)) · (n̄/(n̄+1))ⁿ`. -/
def thermalProb (nbar : ℝ) (n : ℕ) : ℝ := (1 / (nbar + 1)) * thermalRatio nbar ^ n

variable {nbar : ℝ}













/-! ## Normalization and moments -/











/-! ## The temperature -/

/-- The chapter's **effective Softmax temperature** of a displaced thermal state
with mean occupation `n̄`: `τ = n̄ + 1/2`. -/
def thermalTemperature (nbar : ℝ) : ℝ := nbar + 1 / 2









end BookProof.ChapterCoherentTemperature

end


