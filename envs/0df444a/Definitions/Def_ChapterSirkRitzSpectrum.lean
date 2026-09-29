-- Prove2me | Definitions.Def_ChapterSirkRitzSpectrum
-- name    : ChapterSirkRitzSpectrum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T04:06:07.899751+00:00
-- url     : https://prove2.me/theorems/1f1320e1-5e1e-4de4-a472-d5e524fadfa6
-- title:
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 2, QYM**: "the Friedrichs route gives the resolvent geometry; missing … the statement ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkRitzSpectrum`, source chapter `BookProof/ChapterSirkRitzSpectrum.lean`).
--
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 2, QYM**: "the Friedrichs route gives the resolvent geometry; missing … the statement that the Ritz/gap values converge to the *spectrum* of the Friedrichs extension as `m → ∞`".
--
--   `BookProof.HermiteGalerkin.ritzInf_tendsto_domainInf` already proves that the Rayleigh–Ritz values of the Galerkin truncations decrease to the infimum of the *energy form* over the finite-mode domain. What was missing is the identification of that limit with a *spectral* quantity — the bottom of the spectrum of the selected (Friedrichs) extension. This chapter supplies the missing link and the assembled statement.
--
--   * `rayleighSet` / `rayleighInf` — the Rayleigh quotients of the unit vectors of a bounded operator, and their infimum. * `le_rayleigh_iff_le_spectrum` — **the numerical characterisation of the bottom of the spectrum**: for a bounded self-adjoint operator `T` and a real `c`, `c‖x‖² ≤ ⟪Tx, x⟫` for every `x` **iff** `c ≤ μ` for every `μ ∈ spectrum ℝ T`. * `spectrum_real_nonempty`, `spectrum_real_bddBelow` — the real spectrum of a bounded self-adjoint operator on a nonzero Hilbert space is a nonempty set that is bounded below (by `−‖T‖`). * `sInf_spectrum_eq_rayleighInf` — **the bottom of the spectrum is the bottom of the numerical range**, `sInf (spectrum ℝ T) = rayleighInf T`. * `ritzInf_finiteModeDomain_eq_rayleighInf` — the Ritz infimum over the finite-mode (Hermite) domain equals the Rayleigh infimum over the whole space: the truncation domain is dense, and the Rayleigh quotient is continuous. * `ritzInf_tendsto_sInf_spectrum` — **headline**: for a bounded positive self-adjoint operator, the Rayleigh–Ritz values of the Hermite–Galerkin truncations converge to `sInf (spectrum ℝ A)`. * `galerkin_ritz_tendsto_sInf_spectrum_of_selected` — the same statement with the extension named: the limit is the bottom of the spectrum of the operator the Galerkin/Hashimoto algorithm *selects* (the positive self-adjoint extension of the matrix, which for the bounded regime is the Friedrichs extension of `BookProof.YangMillsFriedrichsLimit`).
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkRitzSpectrum.lean

import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib

import Mathlib

/-!
# Chapter SirkRitzSpectrum — the Rayleigh–Ritz values converge to the bottom of the
spectrum

`CONSOLIDATED_PLAN.md` §12.2 **Gap 2, QYM**: "the Friedrichs route gives the
resolvent geometry; missing … the statement that the Ritz/gap values converge to
the *spectrum* of the Friedrichs extension as `m → ∞`".

`BookProof.HermiteGalerkin.ritzInf_tendsto_domainInf` already proves that the
Rayleigh–Ritz values of the Galerkin truncations decrease to the infimum of the
*energy form* over the finite-mode domain.  What was missing is the identification
of that limit with a *spectral* quantity — the bottom of the spectrum of the
selected (Friedrichs) extension.  This chapter supplies the missing link and the
assembled statement.

## Deliverables

* `rayleighSet` / `rayleighInf` — the Rayleigh quotients of the unit vectors of a
  bounded operator, and their infimum.
* `le_rayleigh_iff_le_spectrum` — **the numerical characterisation of the bottom of
  the spectrum**: for a bounded self-adjoint operator `T` and a real `c`,
  `c‖x‖² ≤ ⟪Tx, x⟫` for every `x` **iff** `c ≤ μ` for every `μ ∈ spectrum ℝ T`.
* `spectrum_real_nonempty`, `spectrum_real_bddBelow` — the real spectrum of a
  bounded self-adjoint operator on a nonzero Hilbert space is a nonempty set that
  is bounded below (by `−‖T‖`).
* `sInf_spectrum_eq_rayleighInf` — **the bottom of the spectrum is the bottom of the
  numerical range**, `sInf (spectrum ℝ T) = rayleighInf T`.
* `ritzInf_finiteModeDomain_eq_rayleighInf` — the Ritz infimum over the finite-mode
  (Hermite) domain equals the Rayleigh infimum over the whole space: the truncation
  domain is dense, and the Rayleigh quotient is continuous.
* `ritzInf_tendsto_sInf_spectrum` — **headline**: for a bounded positive
  self-adjoint operator, the Rayleigh–Ritz values of the Hermite–Galerkin
  truncations converge to `sInf (spectrum ℝ A)`.
* `galerkin_ritz_tendsto_sInf_spectrum_of_selected` — the same statement with the
  extension named: the limit is the bottom of the spectrum of the operator the
  Galerkin/Hashimoto algorithm *selects* (the positive self-adjoint extension of
  the matrix, which for the bounded regime is the Friedrichs extension of
  `BookProof.YangMillsFriedrichsLimit`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterSirkRitzSpectrum

open BookProof.FarisLavine BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## 1. Two elementary identities -/







/-! ## 2. The numerical characterisation of the bottom of the spectrum -/













/-! ## 3. The bottom of the spectrum as an infimum of Rayleigh quotients -/

/-- The set of Rayleigh quotients of the unit vectors of a bounded operator. -/
def rayleighSet (T : F →L[ℂ] F) : Set ℝ :=
  {t : ℝ | ∃ x : F, ‖x‖ = 1 ∧ t = (inner ℂ x (T x) : ℂ).re}

/-- The bottom of the numerical range. -/
def rayleighInf (T : F →L[ℂ] F) : ℝ := sInf (rayleighSet T)











/-! ## 4. The Ritz infimum over the finite-mode domain is the Rayleigh infimum -/











/-! ## 5. The headline: Ritz values converge to the bottom of the spectrum -/





end BookProof.ChapterSirkRitzSpectrum


