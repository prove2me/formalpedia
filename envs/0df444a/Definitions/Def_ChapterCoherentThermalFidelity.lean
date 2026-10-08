-- Prove2me | Definitions.Def_ChapterCoherentThermalFidelity
-- name    : ChapterCoherentThermalFidelity
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T14:50:11.154167+00:00
-- url     : https://prove2.me/theorems/3d9b6582-7944-45be-a83e-fa4ca6ef806d
-- title:
--   Chapter CoherentThermalFidelity
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCoherentThermalFidelity.lean`): generated def bundle for ChapterCoherentThermalFidelity. See BookProof/ChapterCoherentThermalFidelity.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCoherentThermalFidelity.lean

import Definitions.Def_ChapterThermalTemperatureCore
import Definitions.Def_ChapterCoherentFidelity
import Definitions.Def_ChapterDisplacedThermalOverlap
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterCoherentTemperature
import Mathlib


/-!
# Where the extra `½` comes from: the fidelity of a displaced thermal state with a
coherent state (plan GAP-1, Part A.4 / F.4)

`ChapterCoherentTemperature` *defines* the chapter's temperature as `τ = n̄ + ½`,
`ChapterThermalTemperatureCore` proves the occupation-number identities behind it,
and `ChapterDisplacedThermalOverlap` models a displaced thermal state by a
Gaussian whose variance is `n̄ + ½` — but in that Gaussian model the zero-point
half is *put in by hand* (it is the variance of the vacuum noise the model
convolves with).

This module removes that postulate.  The extra `½` is derived from the
**coherent-state overlap** by a computation carried out entirely in
occupation-number (Fock) coordinates:

* `coherentThermalFidelity nbar lam` is the fidelity `⟨β| ρ_th(n̄) |β⟩` of a
  thermal state of mean occupation `n̄` with a coherent state of intensity
  `λ = ‖β‖²`, written as the sum `∑ₙ |⟨β|n⟩|² · Pr_th(n)` of the coherent
  (Poisson) occupation statistics against the thermal (geometric) ones;
* `coherentThermalFidelity_eq` — the closed form
  `⟨β|ρ_th|β⟩ = exp(−λ/(n̄+1)) / (n̄+1)`: a Gaussian in the phase-space distance
  `λ = ‖β‖²` whose **width is `n̄ + 1`**;
* `coherentThermalFidelity_vacuum_eq_fidelityC` — at `n̄ = 0` the same expression
  *is* the coherent-state fidelity `exp(−‖q−k‖²)` of `ChapterCoherentFidelity`,
  the Born numerator of the attention weight.  So the coherent state contributes
  width `½` to an overlap (`fidelityC_width`: two coherent states give width
  `½ + ½ = 1`);
* `coherentThermalFidelity_width_eq` — the width of the thermal–coherent fidelity
  splits as `n̄ + 1 = τ + ½` with `τ = n̄ + ½`: the thermal state's own width plus
  the coherent probe's zero-point half.  Widths add, and the half in `τ` is
  exactly the coherent-state half;
* `thermalTemperature_eq_fidelity_width_sub_coherent_half` — **headline**: the
  temperature is *read off* the fidelity rather than postulated.  If the
  thermal–coherent fidelity is the Gaussian `exp(−λ/w)/w` of some width `w > 0`,
  then necessarily `τ = w − ½`, the subtracted `½` being the coherent-state width
  `coherentWidth` fixed by the coherent–coherent overlap;
* `dtOverlap_coherentParameter` and `dtOverlap_width_eq_two_tau` — the same
  additivity checked against the Gaussian model of
  `ChapterDisplacedThermalOverlap`: in the dimensionless coherent parameter
  (`x = √2·α`) the overlap of two displaced thermal states is
  `exp(−‖α₁−α₂‖²/(2τ))`, i.e. width `τ + τ`, and at `n̄ = 0` this is again the
  coherent-state overlap.  The Fock computation and the Gaussian model therefore
  agree, and both assign the coherent state the width `½`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterCoherentThermalFidelity

open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

/-! ## The thermal–coherent fidelity in Fock coordinates -/

/-- The **fidelity of a thermal state with a coherent state**, `⟨β|ρ_th(n̄)|β⟩`,
computed in occupation-number coordinates: the coherent (Poisson) occupation
probabilities `|⟨β|n⟩|² = e^{−λ}λⁿ/n!` at intensity `λ = ‖β‖²`, paired against the
thermal (geometric) occupation probabilities of the bath. -/
def coherentThermalFidelity (nbar lam : ℝ) : ℝ :=
  ∑' n : ℕ, coherentOccupation lam n * thermalProb nbar n







/-! ## The vacuum case *is* the coherent-state overlap -/





/-- The **width a coherent state contributes to an overlap**: one half.  (The
overlap of two coherent states has Gaussian width `coherentWidth + coherentWidth
= 1`, see `fidelityC_width`.) -/
def coherentWidth : ℝ := 1 / 2





/-! ## Widths add: `n̄ + 1 = τ + ½` -/











/-! ## Cross-check against the Gaussian phase-space model -/







end BookProof.ChapterCoherentThermalFidelity

end


