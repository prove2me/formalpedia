-- Prove2me | Definitions.Def_ChapterQedFockGapChain
-- name    : ChapterQedFockGapChain
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-30T08:27:02.744774+00:00
-- url     : https://prove2.me/theorems/508770fe-00f7-4c5f-ae3f-e4d0da1dcc79
-- title:
--   ChapterQedFockGapChain
-- statement:
--   ChapterQedFockGapChain

import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib


/-!
# Chapter QedFockGapChain — the gap chain for QED, and what masslessness costs

`CONSOLIDATED_PLAN.md`, next-steps item **2** of the 2026-08-28j block: *instantiate the
chain for QED — and say what the masslessness means.*

The free photon's one-particle energy is diagonal in the mode basis with the massless
dispersion `ω_k = |k|`, so the diagonal chain of `ChapterFockDiagonalGapChain` applies
directly — but only at `m = 0`.  This module records exactly that, and, so that the
statement cannot be misread as a photon mass gap, it also *proves the obstruction*: if the
momentum assignment accumulates at zero (the physical infrared situation), then for every
`m > 0` the one-particle form gap `⟪x, D x⟫ ≥ m‖x‖²` is **false** on the core.

## What is proved

* `diagOnePart_quadForm_basis` — the diagonal form on a single mode is that mode's energy.
* `diagOnePart_no_form_gap` — *no* form gap above any mode energy: if `ω_k < m` for some
  mode `k`, there is a unit core vector on which the diagonal form is `< m‖x‖²`.
* `photonDispersion`, `photonDispersion_nonneg` — the massless dispersion `ω_k = |p_k|`.
* **`photon_fock_positivity`** — the honest unconditional QED statement: the second
  quantization of the photon energy annihilates the outer vacuum and is non-negative on
  every finite-particle state.  This is `diag_fock_gap` at `m = 0`; the gap is `0`.
* **`photon_no_one_particle_gap`** — the obstruction: for an infrared-accumulating momentum
  assignment (`∀ ε > 0, ∃ k, |p_k| < ε`) and *every* `m > 0`, the one-particle form gap
  fails.  So no instantiation of the chain can produce a positive photon mass gap.
* **`irPhoton_fock_mass_gap`** — with an infrared regulator `μ > 0` imposed on the mode
  energies (`ω_k = max μ |p_k|`), the diagonal chain gives the nested-Fock mass gap `μ`.
* **`proca_fock_mass_gap`** — with a massive (Proca-type) one-particle energy
  `ω_k = √(p_k² + m²)`, `m > 0`, the chain gives the nested-Fock mass gap `m`.

## Honest boundary

The free-photon instantiation yields positivity and **no gap**; that is a feature of
massless dispersion, not a deficiency of the chain, and `photon_no_one_particle_gap` proves
that no positive gap is available at the one-particle level in the infrared-accumulating
case.  The gapped statements above are statements about the *regulated* (`μ > 0`) and
*massive* (Proca) one-particle energies, which are modelling replacements for the photon
energy, not theorems about physical QED.  No photon mass is claimed anywhere.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

namespace BookProof.QedFockGapChain

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FarisLavine
open BookProof.HermiteGalerkin BookProof.HermiteCore
open BookProof.FockDiagonalGapChain BookProof.YangMillsFriedrichs
open MeasureTheory

section General

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]





end General

/-! ## 1. The free photon: positivity, and no gap -/

/-- **The massless photon dispersion** `ω_k = |p_k|` of the mode `k`. -/
def photonDispersion (p : ℕ → ℝ) (k : ℕ) : ℝ := |p k|







/-! ## 2. What restores a gap: an infrared regulator, or a mass -/

/-- **The infrared-regulated photon energy** `ω_k = max μ |p_k|`: every mode energy is at
least the regulator `μ`. -/
def irPhotonDispersion (mu : ℝ) (p : ℕ → ℝ) (k : ℕ) : ℝ := max mu |p k|







end BookProof.QedFockGapChain

end


