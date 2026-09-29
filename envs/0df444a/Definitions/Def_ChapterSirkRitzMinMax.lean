-- Prove2me | Definitions.Def_ChapterSirkRitzMinMax
-- name    : ChapterSirkRitzMinMax
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T09:14:30.693825+00:00
-- url     : https://prove2.me/theorems/5da4305e-87af-4c76-96aa-edefdbeab5a4
-- title:
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 2, QYM** asks for "the statement that the Ritz/**gap** values converge to the spectru ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkRitzMinMax`, source chapter `BookProof/ChapterSirkRitzMinMax.lean`).
--
--   `CONSOLIDATED_PLAN.md` §12.2 **Gap 2, QYM** asks for "the statement that the Ritz/**gap** values converge to the spectrum of the selected extension as `m → ∞`". `BookProof.ChapterSirkRitzSpectrum` settled the *lowest* Ritz value: it converges to `sInf (spectrum ℝ A)`. A gap statement needs the **second** level as well, and there is no second Rayleigh quotient — the correct object is the Courant–Fischer min–max level
--
--   `minmaxLevel T k = inf { sup_{x ∈ S, ‖x‖ = 1} ⟪x, Tx⟫ : dim S = k + 1 }`.
--
--   This chapter introduces those levels for a bounded operator on a complex Hilbert space, and proves that the **Galerkin (Rayleigh–Ritz) min–max levels of the truncations converge to them**, hence that the computed gap converges to the min–max gap.
--
--   * `rayleighVal`, `rayleighSetOn`, `rayleighSup` — the Rayleigh quotient, its range over the unit sphere of a subspace, and the supremum, with the basic bounds (`rayleighSup_le_norm`, `rayleighSup_mono`). * `minmaxLevel` / `minmaxLevelIn` — the Courant–Fischer levels of `T`, and the levels computed inside a fixed subspace `W` (the truncation the solver sees). * `minmaxLevel_le_minmaxLevelIn` — the Ritz levels are always **upper** bounds (the variational principle in the direction the algorithm can certify). * `minmaxLevel_mono` — the levels increase with `k`. * `minmaxLevel_zero_eq_rayleighInf` and `minmaxLevel_zero_eq_sInf_spectrum` — the level `k = 0` is the bottom of the numerical range, hence the bottom of the spectrum: this chapter's ladder starts exactly where `ChapterSirkRitzSpectrum` stopped. * `exists_galerkin_approx_subspace` — the approximation engine: any `(k+1)`-dimensional subspace can be pushed into a large enough Galerkin subspace with an arbitrarily small increase of its Rayleigh supremum. * `galerkin_minmaxLevel_tendsto` — **headline**: for every `k`, the Galerkin min–max levels converge to `minmaxLevel T k`. * `galerkin_gap_tendsto` — the computed **gap** `Λ₁(m) − Λ₀(m)` converges to `minmaxLevel T 1 − minmaxLevel T 0`, and `galerkin_gap_eventually_pos`: a positive min–max gap is eventually seen by the truncations.
--
--   The min–max levels are spectral quantities only below the essential spectrum; nothing here claims that `minmaxLevel T k` is an eigenvalue for `k ≥ 1` (for `k = 0` the identification with `sInf (spectrum ℝ T)` *is* proved). The operator is bounded throughout — the unbounded case is reached through the resolvent, not directly.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkRitzMinMax.lean

import Definitions.Def_ChapterSirkRitzSpectrum
import Mathlib

import Mathlib

/-!
# Chapter SirkRitzMinMax — the higher Rayleigh–Ritz levels and the Ritz gap

`CONSOLIDATED_PLAN.md` §12.2 **Gap 2, QYM** asks for "the statement that the
Ritz/**gap** values converge to the spectrum of the selected extension as `m → ∞`".
`BookProof.ChapterSirkRitzSpectrum` settled the *lowest* Ritz value: it converges to
`sInf (spectrum ℝ A)`.  A gap statement needs the **second** level as well, and there
is no second Rayleigh quotient — the correct object is the Courant–Fischer min–max
level

  `minmaxLevel T k = inf { sup_{x ∈ S, ‖x‖ = 1} ⟪x, Tx⟫ : dim S = k + 1 }`.

This chapter introduces those levels for a bounded operator on a complex Hilbert
space, and proves that the **Galerkin (Rayleigh–Ritz) min–max levels of the
truncations converge to them**, hence that the computed gap converges to the
min–max gap.

## Deliverables

* `rayleighVal`, `rayleighSetOn`, `rayleighSup` — the Rayleigh quotient, its range
  over the unit sphere of a subspace, and the supremum, with the basic bounds
  (`rayleighSup_le_norm`, `rayleighSup_mono`).
* `minmaxLevel` / `minmaxLevelIn` — the Courant–Fischer levels of `T`, and the
  levels computed inside a fixed subspace `W` (the truncation the solver sees).
* `minmaxLevel_le_minmaxLevelIn` — the Ritz levels are always **upper** bounds
  (the variational principle in the direction the algorithm can certify).
* `minmaxLevel_mono` — the levels increase with `k`.
* `minmaxLevel_zero_eq_rayleighInf` and `minmaxLevel_zero_eq_sInf_spectrum` — the
  level `k = 0` is the bottom of the numerical range, hence the bottom of the
  spectrum: this chapter's ladder starts exactly where `ChapterSirkRitzSpectrum`
  stopped.
* `exists_galerkin_approx_subspace` — the approximation engine: any `(k+1)`-dimensional
  subspace can be pushed into a large enough Galerkin subspace with an arbitrarily
  small increase of its Rayleigh supremum.
* `galerkin_minmaxLevel_tendsto` — **headline**: for every `k`, the Galerkin min–max
  levels converge to `minmaxLevel T k`.
* `galerkin_gap_tendsto` — the computed **gap** `Λ₁(m) − Λ₀(m)` converges to
  `minmaxLevel T 1 − minmaxLevel T 0`, and `galerkin_gap_eventually_pos`: a positive
  min–max gap is eventually seen by the truncations.

## Honest boundary

The min–max levels are spectral quantities only below the essential spectrum;
nothing here claims that `minmaxLevel T k` is an eigenvalue for `k ≥ 1` (for
`k = 0` the identification with `sInf (spectrum ℝ T)` *is* proved).  The operator is
bounded throughout — the unbounded case is reached through the resolvent, not
directly.
-/

noncomputable section

namespace BookProof.RitzMinMax

open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## 1. Rayleigh quotients on a subspace -/

/-- The Rayleigh quotient `⟪x, Tx⟫` (real part) of a vector. -/
def rayleighVal (T : F →L[ℂ] F) (x : F) : ℝ := (inner ℂ x (T x) : ℂ).re

/-- The Rayleigh quotients of the unit vectors of a subspace. -/
def rayleighSetOn (T : F →L[ℂ] F) (S : Submodule ℂ F) : Set ℝ :=
  {t : ℝ | ∃ x : F, x ∈ S ∧ ‖x‖ = 1 ∧ t = rayleighVal T x}

/-- The top of the numerical range of `T` on a subspace. -/
def rayleighSup (T : F →L[ℂ] F) (S : Submodule ℂ F) : ℝ := sSup (rayleighSetOn T S)





























/-! ## 2. The Courant–Fischer levels -/

/-- The values `sup_{x ∈ S, ‖x‖ = 1} ⟪x, Tx⟫` over the `(k+1)`-dimensional subspaces. -/
def minmaxSet (T : F →L[ℂ] F) (k : ℕ) : Set ℝ :=
  {t : ℝ | ∃ S : Submodule ℂ F, Module.finrank ℂ S = k + 1 ∧ t = rayleighSup T S}

/-- The `k`-th Courant–Fischer min–max level of a bounded operator. -/
def minmaxLevel (T : F →L[ℂ] F) (k : ℕ) : ℝ := sInf (minmaxSet T k)

/-- The same values, computed only inside a fixed subspace `W`: the Ritz levels the
solver produces from the truncation to `W`. -/
def minmaxSetIn (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) : Set ℝ :=
  {t : ℝ | ∃ S : Submodule ℂ F, S ≤ W ∧ Module.finrank ℂ S = k + 1 ∧ t = rayleighSup T S}

/-- The `k`-th Rayleigh–Ritz level of the truncation to `W`. -/
def minmaxLevelIn (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) : ℝ := sInf (minmaxSetIn T W k)













/-! ## 3. Level zero is the bottom of the numerical range -/







/-! ## 4. The Galerkin flag: dimensions and approximation -/







/-! ## 5. The headline: convergence of the Galerkin min–max levels -/











end BookProof.RitzMinMax


