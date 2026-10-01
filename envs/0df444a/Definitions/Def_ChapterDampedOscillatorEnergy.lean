-- Prove2me | Definitions.Def_ChapterDampedOscillatorEnergy
-- name    : ChapterDampedOscillatorEnergy
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:38:33.669337+00:00
-- url     : https://prove2.me/theorems/c4c012b9-c403-483f-9fed-caf396648c9c
-- title:
--   Chapter DampedOscillatorEnergy
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterDampedOscillatorEnergy.lean`): generated def bundle for ChapterDampedOscillatorEnergy. See BookProof/ChapterDampedOscillatorEnergy.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDampedOscillatorEnergy.lean

import Mathlib


/-!
# The damped coupled oscillators: no conserved energy, but conserved probability

This module formalizes the concrete example of the section *"Wave-function
parametrization of dissipative dynamics"* of `book.tex` (lines 2184–2222), the
two classical coupled oscillators with different frequencies and different
damping constants,

```
ẍ₁ + λ₁ ẋ₁ + ω₁² x₁ − c x₂ = 0,
ẍ₂ + λ₂ ẋ₂ + ω₂² x₂ − c x₁ = 0,
```

about which the manuscript says: *"Since this system is dissipative, it cannot
have a conserved Energy but the pendulums do not disappear and thus the
probability is conserved."*

## Results

* `hasDerivAt_dampedEnergy`, `dampedEnergy_antitone`,
  `dampedEnergy_not_constant_of_damped` — for a single damped oscillator the
  mechanical energy `½ẋ² + ½ω²x²` has derivative `−λ ẋ²`; it is therefore
  non-increasing when the damping is non-negative, and it is *not* conserved as
  soon as the damping is positive and the oscillator is moving at some instant.
* `hasDerivAt_coupledEnergy`, `coupledEnergy_antitone`,
  `coupledEnergy_not_constant_of_damped` — the same three statements for the
  book's coupled pair, whose energy `½(ẋ₁² + ẋ₂²) + ½(ω₁²x₁² + ω₂²x₂²) − c x₁x₂`
  decays at the rate `−λ₁ẋ₁² − λ₂ẋ₂²`.
* `criticallyDamped_isSolution`, `criticallyDamped_energy`,
  `criticallyDamped_energy_strictAnti` — a completely explicit non-trivial
  solution (`x t = e^{−t}` with `λ = 2`, `ω = 1`) whose energy `e^{−2t}` is
  strictly decreasing: the dissipation statement is not vacuous.
* `total_probability_conserved` — meanwhile the total probability *is* conserved
  by any (measurable) deterministic evolution of the state: the pushforward of a
  probability measure along the evolution is again a probability measure.  This
  is the manuscript's reason to parametrize the state by a wave-function rather
  than by a conserved energy.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.DampedOscillatorEnergy

open MeasureTheory

/-! ## 1. One damped oscillator -/

/-- The mechanical energy `½ẋ² + ½ω²x²` of an oscillator with position `x` and
velocity `v`. -/
noncomputable def dampedEnergy (omega : ℝ) (x v : ℝ → ℝ) (t : ℝ) : ℝ :=
  v t ^ 2 / 2 + omega ^ 2 * x t ^ 2 / 2







/-! ## 2. The book's coupled pair -/

/-- The energy of the coupled pair, including the coupling term. -/
noncomputable def coupledEnergy (omega1 omega2 c : ℝ) (x1 x2 v1 v2 : ℝ → ℝ) (t : ℝ) : ℝ :=
  v1 t ^ 2 / 2 + v2 t ^ 2 / 2 + omega1 ^ 2 * x1 t ^ 2 / 2 + omega2 ^ 2 * x2 t ^ 2 / 2
    - c * (x1 t * x2 t)







/-! ## 3. An explicit dissipating solution -/















/-! ## 4. Probability is conserved -/



end BookProof.DampedOscillatorEnergy


