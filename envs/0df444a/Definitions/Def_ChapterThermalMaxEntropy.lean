-- Prove2me | Definitions.Def_ChapterThermalMaxEntropy
-- name    : ChapterThermalMaxEntropy
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:29:02.326284+00:00
-- url     : https://prove2.me/theorems/2f019238-f2ed-4e61-8cfe-f0533a6f26bf
-- title:
--   Chapter ThermalMaxEntropy
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterThermalMaxEntropy.lean`): generated def bundle for ChapterThermalMaxEntropy. See BookProof/ChapterThermalMaxEntropy.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterThermalMaxEntropy.lean

import Definitions.Def_ChapterCoherentTemperature
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
import Mathlib


/-!
# Chapter "The Coherent State of Attention", §"Temperature and the Thermal Bath" —
why the bath is *thermal*: the maximum-entropy characterization

`ChapterCoherentTemperature` postulates the Bose–Einstein / geometric occupation
law and computes its moments; `ChapterCoherentOccupation` identifies the
chapter's temperature `τ = n̄ + 1/2` with the mean oscillator energy, and
`ChapterBoseEinstein` identifies the law itself with the Gibbs law
`Pr(n) ∝ e^{-n x}`.  What none of them proves is *why* that law —
the physical answer being the variational one: among all occupation
distributions with a prescribed mean occupation `n̄`, the thermal law is the one
of **maximal Shannon entropy**.  That is proved here.

## Deliverables

* `thermalEntropy` — the Shannon entropy `-∑ₙ Pr(n) log Pr(n)` of the thermal
  law, and `thermalEntropy_eq`: its closed form
  `log(n̄+1) - n̄ log(n̄/(n̄+1))`;
* `thermalEntropy_boseEinstein` — in Gibbs variables,
  `S(x) = -log(1 - e^{-x}) + x·n̄(x)`, the textbook oscillator entropy;
* `gibbs_pointwise` — the pointwise Gibbs inequality
  `p·log q - p·log p ≤ q - p` (from `log y ≤ y - 1`), valid also at `p = 0`;
* `shannonEntropy_le_thermalEntropy` — **the headline**: any finitely supported
  occupation distribution `p` with mean occupation `n̄` has Shannon entropy at
  most `thermalEntropy n̄`.

The bound is not vacuous: it is the entropy of an actual distribution with that
mean occupation (`thermalProb_tsum_one`, `thermalProb_mean` in
`ChapterCoherentTemperature`), which the finitely supported competitors
approximate.

The support hypothesis (a `Finset`) keeps the competitor side elementary and
`sorry`-free; the thermal side is the genuine infinite sum.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterThermalMaxEntropy

open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {nbar : ℝ}

/-! ## The thermal entropy -/





/-- The **Shannon entropy of the thermal occupation law**. -/
def thermalEntropy (nbar : ℝ) : ℝ :=
  -∑' n : ℕ, thermalProb nbar n * Real.log (thermalProb nbar n)





/-! ## The Gibbs inequality and the maximum-entropy property -/





end BookProof.ChapterThermalMaxEntropy

end


