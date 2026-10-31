-- Prove2me | Definitions.Def_ChapterNsCutoffUniformity
-- name    : ChapterNsCutoffUniformity
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-30T08:29:21.51413+00:00
-- url     : https://prove2.me/theorems/022f59fb-c586-4fb1-81ee-69da5942ebaf
-- title:
--   Chapter NsCutoffUniformity
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsCutoffUniformity.lean`): generated def bundle for ChapterNsCutoffUniformity. See BookProof/ChapterNsCutoffUniformity.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsCutoffUniformity.lean

import Definitions.Def_ChapterNsFourierElimination
import Definitions.Def_ChapterNavierStokesFullEulerianFock
import Mathlib


/-!
# Uniformity of the reduced forms under the energy cutoff

The first of the two residual obligations of item 4 of the Navier–Stokes plan items of
`CONSOLIDATED_PLAN.md` (§5.4(1) of `DESIGN_COMPARISON_N_20260915.md`): after the Fourier
elimination the reduced constraint forms carry the mode coefficients `i k_j` and `−|k|²`, and
under the energy cutoff `|k_j| ≤ Λ` they must be bounded by `O(Λ)` **uniformly in the parcel
number `n`** — that uniformity is what makes the `ℓ²`-lift of the sector Hamiltonians possible,
and it is why the cutoff is load-bearing rather than cosmetic.

What is proved here about the reduced family `redFormPoly` of
`BookProof.ChapterNsFourierElimination`:

* `norm_coeff_redVisc_le`, `norm_coeff_redAdvectPoly_le`, `norm_coeff_redMomentumPoly_le` and the
  headline `norm_coeff_redFormPoly_le` — **every coefficient of every reduced form of every parcel
  is bounded by `cutoffBound nu Λ = 1 + 3Λ + 3|ν|Λ²`** as soon as `|k_j| ≤ Λ`.  The bound does not
  depend on the parcel number `n`, on the parcel `p`, on which of the seven forms is taken, or on
  the monomial: it is `O(Λ)` in exactly the sense the obligation asks for (and `O(Λ²)` through the
  viscous coefficient `ν|k|²`);
* `totalDegree_redFormPoly_le` — the reduced forms are of degree at most two, again uniformly;
* `vars_redFormPoly_subset` — **parcel locality**: a reduced form involves only the six
  coordinates of its own parcel.  With the fixed number `7` of forms per parcel this is the
  sparsity that makes the row/column (Schur) data of the sector Hamiltonians independent of `n`;
* `norm_coeff_redFormPoly_unbounded_of_no_cutoff` — the cutoff is **necessary**: without it the
  coefficients of the reduced family are unbounded, since the advection coefficient is `k_j`
  itself.

**What this does and does not settle.**  It settles the coefficient half of the uniformity
obligation — the data entering the Schur bounds are `O(Λ)` and parcel local, uniformly in `n`.
The operator-level relative bound `‖H_n x‖ ≤ K ‖(N_n + 1) x‖` with `K` independent of `n` is not
proved here; on the landed route it is not needed either, because the comparison actually used is
the lifted Friedrichs extension of the reduced Hamiltonian itself
(`BookProof.NsFullEuler.nsRedFullOuterN_esa`), for which the Faris–Lavine commutator constant is
`c = 0`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsCutoffUniformity

open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

/-! ## 1. Coefficient bounds for one monomial -/

variable {ι : Type*}

theorem norm_coeff_X_le (a : ι) (m : ι →₀ ℕ) : ‖coeff m (X a : MvPolynomial ι ℂ)‖ ≤ 1 := by
  classical
  rw [coeff_X']
  split <;> simp

theorem norm_coeff_C_mul_X_le (c : ℂ) (a : ι) (m : ι →₀ ℕ) :
    ‖coeff m (C c * X a : MvPolynomial ι ℂ)‖ ≤ ‖c‖ := by
  classical
  rw [coeff_C_mul, norm_mul, coeff_X']
  split <;> simp

theorem norm_coeff_C_mul_X_mul_X_le (c : ℂ) (a b : ι) (m : ι →₀ ℕ) :
    ‖coeff m (C c * (X a * X b) : MvPolynomial ι ℂ)‖ ≤ ‖c‖ := by
  classical
  have hx : (X a * X b : MvPolynomial ι ℂ)
      = monomial (Finsupp.single a 1 + Finsupp.single b 1) 1 := by
    rw [X, X, monomial_mul, one_mul]
  rw [hx, coeff_C_mul, norm_mul, coeff_monomial]
  split <;> simp

/-! ## 2. The cutoff bound -/

/-- The uniform bound on the coefficients of the reduced forms under the cutoff `|k_j| ≤ Λ`. -/
def cutoffBound (nu Λ : ℝ) : ℝ := 1 + 3 * Λ + 3 * |nu| * Λ ^ 2

theorem cutoffBound_nonneg (nu : ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) : 0 ≤ cutoffBound nu Λ := by
  unfold cutoffBound
  positivity

/-- Under the cutoff the viscous coefficient `ν |k|²` is bounded by `3 |ν| Λ²`. -/
theorem abs_visc_coeff_le {nu Λ : ℝ} {k : Fin 3 → ℝ} (hΛ : 0 ≤ Λ) (hk : ∀ j, |k j| ≤ Λ) :
    |nu * ∑ j : Fin 3, (k j) ^ 2| ≤ 3 * |nu| * Λ ^ 2 := by
  have hsum : ∑ j : Fin 3, (k j) ^ 2 ≤ 3 * Λ ^ 2 := by
    have hbound : ∀ j : Fin 3, (k j) ^ 2 ≤ Λ ^ 2 := by
      intro j
      have := hk j
      nlinarith [abs_nonneg (k j), sq_abs (k j)]
    calc ∑ j : Fin 3, (k j) ^ 2 ≤ ∑ _j : Fin 3, Λ ^ 2 := Finset.sum_le_sum fun j _ => hbound j
      _ = 3 * Λ ^ 2 := by simp [Finset.sum_const]
  have hnonneg : 0 ≤ ∑ j : Fin 3, (k j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [abs_mul, abs_of_nonneg hnonneg]
  calc |nu| * ∑ j : Fin 3, (k j) ^ 2 ≤ |nu| * (3 * Λ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hsum (abs_nonneg nu)
    _ = 3 * |nu| * Λ ^ 2 := by ring

/-! ## 3. The coefficient bounds of the reduced forms -/

/-- The real residual form has coefficients bounded by `1 + 3|ν|Λ²`. -/
theorem norm_coeff_redVisc_le (nu : ℝ) {Λ : ℝ} {k : Fin 3 → ℝ} (hΛ : 0 ≤ Λ)
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (i : Fin 3) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redVisc nu k n p i)‖ ≤ 1 + 3 * |nu| * Λ ^ 2 := by
  rw [redVisc, coeff_add]
  refine (norm_add_le _ _).trans ?_
  gcongr
  · exact norm_coeff_X_le _ _
  · refine (norm_coeff_C_mul_X_le _ _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_visc_coeff_le hΛ hk









/-! ## 4. Degree and parcel locality -/

section Degree

variable (nu : ℝ) (k : Fin 3 → ℝ)







end Degree



end

end BookProof.NsCutoffUniformity


