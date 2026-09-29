-- Prove2me | Definitions.Def_ChapterBandEnclosure
-- name    : ChapterBandEnclosure
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T10:51:48.96526+00:00
-- url     : https://prove2.me/theorems/09604acb-c314-4fb2-9330-4af701110c87
-- title:
--   `CONSOLIDATED_PLAN.md` (top work package, "Hashimoto observable to the real-Hamiltonian gap") left exactly one hypothesi ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.BandEnclosure`, source chapter `BookProof/ChapterBandEnclosure.lean`).
--
--   `CONSOLIDATED_PLAN.md` (top work package, "Hashimoto observable to the real-Hamiltonian gap") left exactly one hypothesis of `BookProof.FockOneParticleGap` underived: the **band enclosure**
--
--   `∀ m, lam ∈ Set.Icc (lo m) (hi m)`,
--
--   i.e. that every finite certificate brackets the one-particle spectral edge `lam` of the *infinite* selected operator. In `ChapterFockOneParticleGap` that was an assumption. This chapter derives it from material that is already proved in the project:
--
--   * **band nesting** — the order-`m+1` band sits inside the order-`m` band (`ChapterH8.sirk_band_contained`, `sirk_band_contained_le`; abstracted here as `NestedBands`); * **exponential shrinking** — the band widths decay like `e^{−hm}` and hence vanish (`ChapterH6.sirk_error_decay_exponential`), so the nested bands collapse to one point; * **Hashimoto selects the Friedrichs extension, and its Ritz values converge to the edge of the selected operator** — `HermiteGalerkin.finiteModeRestrict_selects_operator` and `ChapterSirkRitzSpectrum.ritzInf_tendsto_sInf_spectrum`.
--
--   The logical skeleton is `band_enclosure_of_nested`: if the order-`m` *approximant* lies in the order-`m` band, the bands nest, and the approximants converge to `lam`, then `lam` lies in **every** band — because for `n ≥ m` the approximant `a n` already lies in the order-`m` band, which is closed. Feeding the Hashimoto/Galerkin Ritz values in as the approximants and the Ritz convergence theorem in as the convergence, the enclosed point is `sInf (spectrum ℝ A)`, the spectral edge of the operator the algorithm selects.
--
--   * `NestedBands`, `nestedBands_le` — nesting of the certified intervals, iterated; * `band_enclosure_of_nested` — **the band-enclosure hypothesis, derived** from nesting and convergence of the approximants; * `band_limit_unique`, `band_enclosure_endpoints_tendsto` — with vanishing widths the nested bands determine a *unique* limiting edge and their endpoints converge to it; * `sirk_nestedBands`, `sirk_band_widths_tendsto_zero`, `sirk_band_enclosure` — the instance carried by the already-proved SIRK band theorems (nesting from `ChapterH8.sirk_band_contained`, exponential collapse from `ChapterH6.sirk_error_decay_exponential`); * `ritz_band_enclosure_of_nested` — **the enclosure for the selected operator**: nested certified bands that contain the Hashimoto/Galerkin Ritz values enclose `sInf (spectrum ℝ A)` of the operator the algorithm selects; * `fock_mass_gap_of_nested_ritz_bands` — the composition with the free `dΓ` lift of `ChapterFockOneParticleGap`: **no enclosure hypothesis is assumed any more** in the bounded selected-operator regime; * `shiftInvert_band_enclosure`, `shiftInvert_widths_tendsto_zero` — the transport of a band enclosure through the Hashimoto shift-invert `lam = nu⁻¹ − γ`, for the unbounded (resolvent) route.
--
--   Everything is `sorry`-free and introduces no axioms.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

import Definitions.Def_ChapterH8
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib

import Mathlib

/-!
# Chapter BandEnclosure — the band-enclosure hypothesis, derived

`CONSOLIDATED_PLAN.md` (top work package, "Hashimoto observable to the real-Hamiltonian
gap") left exactly one hypothesis of `BookProof.FockOneParticleGap` underived: the
**band enclosure**

  `∀ m, lam ∈ Set.Icc (lo m) (hi m)`,

i.e. that every finite certificate brackets the one-particle spectral edge `lam` of the
*infinite* selected operator.  In `ChapterFockOneParticleGap` that was an assumption.
This chapter derives it from material that is already proved in the project:

* **band nesting** — the order-`m+1` band sits inside the order-`m` band
  (`ChapterH8.sirk_band_contained`, `sirk_band_contained_le`; abstracted here as
  `NestedBands`);
* **exponential shrinking** — the band widths decay like `e^{−hm}` and hence vanish
  (`ChapterH6.sirk_error_decay_exponential`), so the nested bands collapse to one point;
* **Hashimoto selects the Friedrichs extension, and its Ritz values converge to the edge
  of the selected operator** — `HermiteGalerkin.finiteModeRestrict_selects_operator` and
  `ChapterSirkRitzSpectrum.ritzInf_tendsto_sInf_spectrum`.

The logical skeleton is `band_enclosure_of_nested`: if the order-`m` *approximant* lies in
the order-`m` band, the bands nest, and the approximants converge to `lam`, then `lam` lies
in **every** band — because for `n ≥ m` the approximant `a n` already lies in the order-`m`
band, which is closed.  Feeding the Hashimoto/Galerkin Ritz values in as the approximants
and the Ritz convergence theorem in as the convergence, the enclosed point is
`sInf (spectrum ℝ A)`, the spectral edge of the operator the algorithm selects.

## Deliverables

* `NestedBands`, `nestedBands_le` — nesting of the certified intervals, iterated;
* `band_enclosure_of_nested` — **the band-enclosure hypothesis, derived** from nesting and
  convergence of the approximants;
* `band_limit_unique`, `band_enclosure_endpoints_tendsto` — with vanishing widths the
  nested bands determine a *unique* limiting edge and their endpoints converge to it;
* `sirk_nestedBands`, `sirk_band_widths_tendsto_zero`, `sirk_band_enclosure` — the
  instance carried by the already-proved SIRK band theorems (nesting from
  `ChapterH8.sirk_band_contained`, exponential collapse from
  `ChapterH6.sirk_error_decay_exponential`);
* `ritz_band_enclosure_of_nested` — **the enclosure for the selected operator**: nested
  certified bands that contain the Hashimoto/Galerkin Ritz values enclose
  `sInf (spectrum ℝ A)` of the operator the algorithm selects;
* `fock_mass_gap_of_nested_ritz_bands` — the composition with the free `dΓ` lift of
  `ChapterFockOneParticleGap`: **no enclosure hypothesis is assumed any more** in the
  bounded selected-operator regime;
* `shiftInvert_band_enclosure`, `shiftInvert_widths_tendsto_zero` — the transport of a
  band enclosure through the Hashimoto shift-invert `lam = nu⁻¹ − γ`, for the unbounded
  (resolvent) route.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

open Filter Topology

namespace BookProof.BandEnclosure

open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8

/-! ## 1. Nested bands -/

/-- The certified intervals **nest**: the order-`m+1` band is contained in the order-`m`
band.  This is the abstract form of `ChapterH8.sirk_band_contained`. -/
def NestedBands (lo hi : ℕ → ℝ) : Prop :=
  ∀ m, Set.Icc (lo (m + 1)) (hi (m + 1)) ⊆ Set.Icc (lo m) (hi m)



/-! ## 2. The band-enclosure hypothesis, derived -/







/-! ## 3. The SIRK bands are an instance: nesting and exponential collapse -/







/-! ## 4. The enclosure for the operator the Hashimoto algorithm selects -/

section Selected

open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]





end Selected

/-! ## 4b. The unbounded route: the certified gap of the Friedrichs extension

The section above needs the selected operator to be bounded, because it uses the
*spectral* edge `sInf (spectrum ℝ A)`.  For the genuinely unbounded Hamiltonian the same
chain works with the **energy form** in place of the spectrum, and nothing has to be
assumed:

* the Hashimoto/Galerkin Ritz values converge to the bottom `ritzInf H (finiteModeDomain b)`
  of the form on the core (`HermiteGalerkin.ritzInf_tendsto_domainInf`, no boundedness);
* hence nested certified bands enclose that bottom (`band_enclosure_of_nested`);
* a band with lower end `≥ μ` therefore gives the core bound `⟪x, H x⟫ ≥ μ‖x‖²`; and
* the Friedrichs extension — the operator the Hashimoto shift-invert selects
  (`FriedrichsExtension.friedrichs_hashimoto_selects`) — inherits it
  (`FriedrichsFormGap.friedrichs_extension_form_gap`). -/

section Unbounded

open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]







end Unbounded

/-! ## 5. Transport through the Hashimoto shift-invert

The unbounded route certifies the bounded resolvent `R = (h₊ + γ)⁻¹`
(`ChapterFriedrichsExtension.friedrichs_hashimoto_selects`), whose relevant spectral value
`nu` is related to the one-particle edge by `lam = nu⁻¹ − γ`.  A band enclosure for `nu`
transports to a band enclosure for `lam` through that (antitone) map, and the transported
widths still vanish. -/





end BookProof.BandEnclosure

end


