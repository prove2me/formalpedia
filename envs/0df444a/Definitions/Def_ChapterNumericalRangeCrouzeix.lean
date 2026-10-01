-- Prove2me | Definitions.Def_ChapterNumericalRangeCrouzeix
-- name    : ChapterNumericalRangeCrouzeix
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:34:08.219343+00:00
-- url     : https://prove2.me/theorems/c9c3d502-5bb2-4342-bba9-ff0811637ffa
-- title:
--   Chapter NumericalRangeCrouzeix
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNumericalRangeCrouzeix.lean`): generated def bundle for ChapterNumericalRangeCrouzeix. See BookProof/ChapterNumericalRangeCrouzeix.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNumericalRangeCrouzeix.lean

import Definitions.Def_ChapterH9
import Mathlib


/-!
# Crouzeix-type inequalities from the numerical range, for general (non-normal) operators

`BookProof.ChapterCrouzeixSelfAdjoint` proves Crouzeix's inequality with constant `1` for
*normal* operators, and records the honest boundary that for a **general non-normal**
operator the bound `‖f(A)‖ ≤ C · sup_Σ |f|` over a convex set `Σ` containing the numerical
range — with its larger constant — is a named hypothesis.

This file removes that boundary in the disc regime, unconditionally and with an explicit
constant, for the analytic functional calculus.  The chain is:

* `NumRadiusLE A r` — the numerical range of `A` lies in the closed disc of radius `r`
  (`numRadiusLE_iff_numRange_subset` identifies this with `numRange A ⊆ closedBall 0 r`).
* `re_inner_sub_smul_nonneg` / `numRadiusLE_of_re_inner_sub_smul_nonneg` — the *Herglotz
  form* of the numerical-radius bound: `w(A) ≤ 1` iff `Re ⟪x, x − z A x⟫ ≥ 0` for every
  `‖z‖ < 1`.  This is the form that composes with the group of `n`-th roots of unity.
* **`numRadiusLE_pow`** — the **Berger power inequality** `w(Aⁿ) ≤ w(A)ⁿ`, proved by
  Pearcy's argument: the partial-fraction decomposition of `(1 − zⁿAⁿ)⁻¹` over the `n`-th
  roots of unity, realized here without any inverses at all, by the explicit vectors
  `u_k = ∑_{m<n} (ωᵏ z)^m Aᵐ y`.
* `norm_le_two_mul_of_numRadiusLE` — `‖A‖ ≤ 2 w(A)` (polarization), hence
  `norm_pow_le_of_numRadiusLE` — `‖Aⁿ‖ ≤ 2 w(A)ⁿ`.
* **`crouzeix_disc`** — the headline: if the numerical range of `A` lies in the closed disc
  of radius `r` and `f(z) = ∑ aₙ zⁿ` satisfies Cauchy's estimate `‖aₙ‖ ≤ M / Rⁿ` on a
  strictly larger disc of radius `R > r`, then the analytic functional calculus
  `f(A) = ∑ aₙ Aⁿ` converges in operator norm and
  `‖f(A)‖ ≤ (1 + 2r/(R − r)) · M`.
  This is a Crouzeix-type inequality for a *general non-normal* operator, with the
  numerical range as the spectral set and an explicit (larger) constant, **proved**.
* `NumBallLE`, `numBallLE_iff_numRange_subset` and `crouzeix_ball` — the same statement for
  a numerical range in an arbitrary closed disc `closedBall c r`, by the shift `A ↦ A - c`:
  `‖∑ aₙ (A - c)ⁿ‖ ≤ (1 + 2r/(R - r)) M` whenever `‖aₙ‖ ≤ M/Rⁿ` and `R > r`.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace

namespace BookProof.ChapterNumericalRangeCrouzeix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical range of `A` lies in the closed disc of radius `r` about the origin,
written as a bound on Rayleigh quotients that is homogeneous in `x`. -/
def NumRadiusLE (A : E →L[ℂ] E) (r : ℝ) : Prop :=
  ∀ x : E, ‖(⟪x, A x⟫_ℂ)‖ ≤ r * ‖x‖ ^ 2





/-! ## The Herglotz form of the numerical-radius bound -/





/-! ## Pearcy's proof of the Berger power inequality -/

/-- The partial-fraction vectors of Pearcy's argument: `u_k = ∑_{m<n} (ωᵏ z)^m Aᵐ y`. -/
noncomputable def pearcyVec (A : E →L[ℂ] E) (c : ℂ) (n : ℕ) (y : E) : E :=
  ∑ m ∈ Finset.range n, c ^ m • (A ^ m) y









/-! ## From the numerical radius to the operator norm -/







/-! ## The Crouzeix-type bound for the analytic functional calculus -/

/-- The analytic functional calculus of a power series: `f(A) = ∑ aₙ Aⁿ`. -/
noncomputable def analyticFC (a : ℕ → ℂ) (A : E →L[ℂ] E) : E →L[ℂ] E :=
  ∑' n : ℕ, a n • A ^ n







/-! ## The shifted disc: a numerical range in an arbitrary closed ball -/

/-- The numerical range of `A` lies in the closed ball of centre `c` and radius `r`: the
numerical radius of the shifted operator `A - c` is at most `r`. -/
def NumBallLE (A : E →L[ℂ] E) (c : ℂ) (r : ℝ) : Prop :=
  NumRadiusLE (A - c • (1 : E →L[ℂ] E)) r







end BookProof.ChapterNumericalRangeCrouzeix


