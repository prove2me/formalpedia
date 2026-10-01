-- Prove2me | Definitions.Def_ChapterDisplacedThermalOverlap
-- name    : ChapterDisplacedThermalOverlap
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:44:02.830713+00:00
-- url     : https://prove2.me/theorems/85586796-96ef-4e9d-81ba-6e14537ef17c
-- title:
--   Chapter DisplacedThermalOverlap
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterDisplacedThermalOverlap.lean`): generated def bundle for ChapterDisplacedThermalOverlap. See BookProof/ChapterDisplacedThermalOverlap.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDisplacedThermalOverlap.lean

import Mathlib


/-!
# The overlap of displaced thermal states, and the temperature of attention

This module supplies the *physical* layer of the temperature identity
`τ = n̄ + ½` that `Book/CoherentState.lean` §"Temperature and the Thermal Bath"
asserts and that `ChapterThermalTemperatureCore` proves in its finite,
occupation-number core.

The model is the standard Gaussian (phase-space) description of a **displaced
thermal state**: along one quadrature its distribution is a Gaussian centred at
the displacement `a` whose variance is the sum of

* the thermal noise, of variance `n̄` (the mean occupation of the bath), and
* the zero-point noise of the vacuum, of variance `½` (the Heisenberg floor).

`thermal_plus_zeroPoint_conv` is exactly that statement: the convolution of the
two noises is the Gaussian of variance `n̄ + ½`, so the width of a displaced
thermal state — its *temperature* `τ` — is `n̄ + ½`
(`displacedThermal_variance`).

From that Gaussian description the **overlap** of two displaced thermal states
is computed in closed form (`dtOverlap_eq`):

`⟨a | b⟩ = exp(−(a−b)² / 4τ) / √(4πτ)`,

a Gaussian in the phase-space distance whose *width is the temperature*.
Normalizing over a finite family of keys, the constant `1/√(4πτ)` cancels and
the Born weights are **exactly a Softmax** over minus the squared distances at
inverse temperature `β = 1/(4τ)` (`dtBorn_eq_softmax`).  Hence the attention
temperature is set by the bath: `β` is strictly decreasing in `n̄`
(`inverseTemperature_strictAnti`), i.e. a hotter bath gives flatter attention,
and at `n̄ → 0` it saturates at the zero-point value `β = ½`
(`inverseTemperature_zero`).

Finally `dtBorn_eq_softmax_coth` writes the same headline in the physical
variable `x = ħω/kT`, where `τ = ½·coth(x/2)` is the Bose–Einstein closed form
already proved in `ChapterBoseEinstein` / `ChapterThermalTemperatureCore`.

## Documented scope

What is proved here is the Gaussian/phase-space derivation of `τ = n̄ + ½` and
of the Gaussian overlap law.  It is not a derivation inside an infinite
dimensional Fock space: the displaced thermal state is *modelled* by its
(exact, textbook) Gaussian quadrature distribution rather than constructed as a
density operator.  Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace BookProof.ChapterDisplacedThermalOverlap

/-! ## The temperature: thermal noise plus the zero point -/

/-- The **temperature** of a thermal bath of mean occupation `nbar`:
`τ = n̄ + ½`, the thermal variance plus the zero-point half. -/
def tauNN (nbar : ℝ≥0) : ℝ≥0 := nbar + 1 / 2











/-- The quadrature distribution of the **displaced thermal state** with
displacement `a` and bath occupation `nbar`. -/
def displacedThermal (a : ℝ) (nbar : ℝ≥0) : Measure ℝ := gaussianReal a (tauNN nbar)





/-! ## The Gaussian overlap law -/



/-- The **overlap** of two displaced thermal states of common bath occupation
`nbar`: the phase-space integral of the product of their quadrature densities. -/
def dtOverlap (nbar : ℝ≥0) (a b : ℝ) : ℝ :=
  ∫ x, gaussianPDFReal a (tauNN nbar) x * gaussianPDFReal b (tauNN nbar) x







/-! ## The Born weights are a Softmax at inverse temperature `1/(4τ)` -/

/-- The **inverse temperature of attention** induced by a bath of mean
occupation `nbar`: `β = 1/(4τ) = 1/(4(n̄+½))`. -/
def inverseTemperature (nbar : ℝ≥0) : ℝ := 1 / (4 * ((nbar : ℝ) + 1 / 2))







/-- The **Born attention weight** of the `j`-th key, read off the displaced
thermal overlaps. -/
def dtBorn {m : ℕ} (nbar : ℝ≥0) (q : ℝ) (k : Fin m → ℝ) (j : Fin m) : ℝ :=
  dtOverlap nbar q (k j) / ∑ l, dtOverlap nbar q (k l)





end BookProof.ChapterDisplacedThermalOverlap

end


