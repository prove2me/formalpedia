-- Prove2me | Definitions.Def_ChapterSirkRitzPerturbation
-- name    : ChapterSirkRitzPerturbation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T09:15:20.165501+00:00
-- url     : https://prove2.me/theorems/40aab9fa-17af-45ab-91e0-08ee2b80dfde
-- title:
--   `BookProof.ChapterSirkRitzMinMax` built the Courant–Fischer levels `minmaxLevel T k` of a bounded operator and proved th ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkRitzPerturbation`, source chapter `BookProof/ChapterSirkRitzPerturbation.lean`).
--
--   `BookProof.ChapterSirkRitzMinMax` built the Courant–Fischer levels `minmaxLevel T k` of a bounded operator and proved that the Galerkin (Rayleigh–Ritz) levels of the truncations converge to them, so that the *computed* gap converges to the min–max gap. That statement is about **one** operator: the exact one. A solver never holds the exact operator — it holds a model of it (a truncated coupling, a rounded matrix, a regularized potential). `CONSOLIDATED_PLAN.md` §12.2 Gap 2 and §13 therefore need the *stability* half: how far can the levels move when the operator moves?
--
--   This chapter answers that: **every Courant–Fischer level is 1-Lipschitz in the operator norm**, so the gap is 2-Lipschitz, and a gap that exceeds twice the modelling error is a genuine gap of the exact operator.
--
--   * `rayleighVal_sub_le_dist`, `abs_rayleighVal_sub_le_dist`, `rayleighSup_le_rayleighSup_add`, `abs_rayleighSup_sub_le_dist` — the elementary layer: on the unit sphere the Rayleigh quotients, and hence the tops of the numerical ranges on any subspace, move by at most `‖T − T'‖`. * `minmaxSet_nonempty_congr` / `minmaxSetIn_nonempty_congr` — the min–max sets are nonempty for one operator iff for all of them: nonemptiness is a statement about the *dimensions* available in the space, not about the operator. * **`abs_minmaxLevel_sub_le_dist`** — the headline: `|Λ_k(T) − Λ_k(T')| ≤ ‖T − T'‖`. * **`abs_minmaxLevelIn_sub_le_dist`** — the same for the Ritz levels computed inside a fixed truncation `W`, and **`minmaxLevel_le_minmaxLevelIn_add`**: a Ritz level computed in `W` for the *model* operator is an upper bound for the exact level of the true operator, up to the operator error. This is the form a certificate takes. * `minmaxLevel_mono_form` — monotonicity in the form order, `minmaxLevel_le_norm` / `neg_norm_le_minmaxLevel` — the levels lie in `[−‖T‖, ‖T‖]`. * `shiftOp`, `rayleighVal_shiftOp`, `rayleighSup_shiftOp`, **`minmaxLevel_shiftOp`** — a real shift shifts every level, `Λ_k(T + c) = Λ_k(T) + c`, hence **`minmaxGap_shiftOp`**: the gap is invariant under the shift a shift-invert scheme applies. * `minmaxGap`, `minmaxGap_nonneg`, `abs_minmaxGap_sub_le` — the gap and its 2-Lipschitz bound; **`minmaxGap_ge_of_dist_le`** and **`minmaxGap_pos_of_dist_lt`**: a gap survives a perturbation of less than half its size. * **`minmaxLevel_tendsto_of_tendsto`** / `minmaxGap_tendsto_of_tendsto` — norm convergence of a family of operators forces convergence of every level, and of the gap. * **`galerkin_model_gap_tendsto`** — what a solver running on the model operator computes: its Galerkin gaps converge, and the limit is within `2ε` of the true gap. * **`galerkin_model_gap_eventually_pos`** — a true gap larger than twice the modelling error is eventually seen by the truncations of the model operator. * **`abs_sInf_spectrum_sub_le_dist`** — through the level-zero identification of `ChapterSirkRitzMinMax`, the bottom of the spectrum of a bounded self-adjoint operator is 1-Lipschitz in the operator norm.
--
--   Everything here is for **bounded** operators, and the distance used is the operator norm: a perturbation that is only relatively bounded, or only strongly convergent, is not covered. The certified direction is the one the variational principle gives: computed Ritz levels are **upper** bounds. Nothing here turns a positive *computed* truncated gap into a positive gap of the exact operator — that needs a lower bound on the first excited level (a residual estimate), not merely the min–max inequality; `galerkin_model_gap_eventually_pos` runs in the sound direction, from a true gap to what the truncations of the model eventually show.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkRitzPerturbation.lean

import Definitions.Def_ChapterSirkRitzMinMax
import Mathlib

import Mathlib

/-!
# Chapter SirkRitzPerturbation — the min–max levels are 1-Lipschitz, and a gap survives a
perturbation

`BookProof.ChapterSirkRitzMinMax` built the Courant–Fischer levels `minmaxLevel T k` of a
bounded operator and proved that the Galerkin (Rayleigh–Ritz) levels of the truncations
converge to them, so that the *computed* gap converges to the min–max gap.  That statement
is about **one** operator: the exact one.  A solver never holds the exact operator — it
holds a model of it (a truncated coupling, a rounded matrix, a regularized potential).
`CONSOLIDATED_PLAN.md` §12.2 Gap 2 and §13 therefore need the *stability* half: how far can
the levels move when the operator moves?

This chapter answers that: **every Courant–Fischer level is 1-Lipschitz in the operator
norm**, so the gap is 2-Lipschitz, and a gap that exceeds twice the modelling error is a
genuine gap of the exact operator.

## Deliverables

* `rayleighVal_sub_le_dist`, `abs_rayleighVal_sub_le_dist`, `rayleighSup_le_rayleighSup_add`,
  `abs_rayleighSup_sub_le_dist` — the elementary layer: on the unit sphere the Rayleigh
  quotients, and hence the tops of the numerical ranges on any subspace, move by at most
  `‖T − T'‖`.
* `minmaxSet_nonempty_congr` / `minmaxSetIn_nonempty_congr` — the min–max sets are nonempty
  for one operator iff for all of them: nonemptiness is a statement about the *dimensions*
  available in the space, not about the operator.
* **`abs_minmaxLevel_sub_le_dist`** — the headline: `|Λ_k(T) − Λ_k(T')| ≤ ‖T − T'‖`.
* **`abs_minmaxLevelIn_sub_le_dist`** — the same for the Ritz levels computed inside a fixed
  truncation `W`, and **`minmaxLevel_le_minmaxLevelIn_add`**: a Ritz level computed in `W`
  for the *model* operator is an upper bound for the exact level of the true operator, up to
  the operator error.  This is the form a certificate takes.
* `minmaxLevel_mono_form` — monotonicity in the form order, `minmaxLevel_le_norm` /
  `neg_norm_le_minmaxLevel` — the levels lie in `[−‖T‖, ‖T‖]`.
* `shiftOp`, `rayleighVal_shiftOp`, `rayleighSup_shiftOp`, **`minmaxLevel_shiftOp`** — a real
  shift shifts every level, `Λ_k(T + c) = Λ_k(T) + c`, hence **`minmaxGap_shiftOp`**: the gap
  is invariant under the shift a shift-invert scheme applies.
* `minmaxGap`, `minmaxGap_nonneg`, `abs_minmaxGap_sub_le` — the gap and its 2-Lipschitz
  bound; **`minmaxGap_ge_of_dist_le`** and **`minmaxGap_pos_of_dist_lt`**: a gap survives a
  perturbation of less than half its size.
* **`minmaxLevel_tendsto_of_tendsto`** / `minmaxGap_tendsto_of_tendsto` — norm convergence of
  a family of operators forces convergence of every level, and of the gap.
* **`galerkin_model_gap_tendsto`** — what a solver running on the model operator computes:
  its Galerkin gaps converge, and the limit is within `2ε` of the true gap.
* **`galerkin_model_gap_eventually_pos`** — a true gap larger than twice the modelling error
  is eventually seen by the truncations of the model operator.
* **`abs_sInf_spectrum_sub_le_dist`** — through the level-zero identification of
  `ChapterSirkRitzMinMax`, the bottom of the spectrum of a bounded self-adjoint operator is
  1-Lipschitz in the operator norm.

## Honest boundary

Everything here is for **bounded** operators, and the distance used is the operator norm: a
perturbation that is only relatively bounded, or only strongly convergent, is not covered.
The certified direction is the one the variational principle gives: computed Ritz levels are
**upper** bounds.  Nothing here turns a positive *computed* truncated gap into a positive
gap of the exact operator — that needs a lower bound on the first excited level (a residual
estimate), not merely the min–max inequality; `galerkin_model_gap_eventually_pos` runs in
the sound direction, from a true gap to what the truncations of the model eventually show.
-/

noncomputable section

namespace BookProof.RitzPerturbation

open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]









/-! ## The min–max levels are 1-Lipschitz -/















/-! ## The order on the forms -/



/-! ## The gap -/

/-- The min–max gap: the distance from the first excited level to the ground level. -/
def minmaxGap (T : F →L[ℂ] F) : ℝ := minmaxLevel T 1 - minmaxLevel T 0







/-- The real shift `T + c` of a bounded operator. -/
def shiftOp (T : F →L[ℂ] F) (c : ℝ) : F →L[ℂ] F :=
  T + (c : ℂ) • ContinuousLinearMap.id ℂ F






















/-! ## What a solver running on the model operator computes -/





end BookProof.RitzPerturbation


