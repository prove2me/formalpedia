-- Prove2me | solution 1 for ArctanTaylor.rem_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:38:16.799071+00:00
-- url     : https://prove2.me/submissions/a4c0b92d-a098-4ef2-b89c-43efde99ce0f

import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-  ArctanTaylor.lean -- ANDÚRIL A4 θ-value instrument: the reusable arctan Taylor bracket.

    The θ-value route (`ThetaValue.lean`) needs, for the Euler/Weierstrass series
    `Im log Γ(x+iy) = y·log n − Σ_k arctan(y/(x+k))` (limit form), a KERNEL box for each
    `arctan(y/(x+k))`.  This file is the reusable arctan instrument that produces those boxes,
    with NO numeric hypotheses and NO special-function anchors (no ψ, no Γ).

    ## The instrument.

    For `u ≥ 0` and any truncation order `N`,

        |arctan u − atanPS u N| ≤ u^(2N+1)/(2N+1),        atanPS u N = Σ_{j<N} (−1)^j u^(2j+1)/(2j+1).

    This is the alternating Taylor bracket, proved RIGOROUSLY from the integral representation
    `arctan u = ∫₀ᵘ (1+t²)⁻¹` (Mathlib `integral_inv_one_add_sq`) via the finite geometric
    identity `(1+t²)⁻¹ = Σ_{j<N}(−t²)^j + (−t²)^N/(1+t²)` and the elementary remainder bound
    `|∫₀ᵘ (−t²)^N/(1+t²)| ≤ ∫₀ᵘ t^(2N) = u^(2N+1)/(2N+1)`.

    Two cheap corollaries used by the tail machinery (elementary, no integral):
      * `arctan_le_self`        : `arctan u ≤ u`               (0 ≤ u)
      * `self_sub_cube_le_arctan`: `u − u³/3 ≤ arctan u`       (0 ≤ u)

    All lemmas are GENERAL in `(u, N)` — the ThetaValue driver instantiates them per term.
    Guarded: `#print axioms arctan_bracket` = {propext, Classical.choice, Quot.sound}.

    conjecture1_proved = False.  A rigorous elementary arctan enclosure, a building block, NOT a
    proof of anything about ζ.
-/





open Real intervalIntegral MeasureTheory

section
namespace ArctanTaylor
end ArctanTaylor
open ArctanTaylor



/-! ### The integral representation split. -/





/-! ### The remainder bound. -/


theorem solution (u : ℝ) (hu : 0 ≤ u) (N : ℕ) :
    |(∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2))| ≤ u^(2*N+1)/(2*N+1) := by
  have hcont : Continuous (fun t : ℝ => (-(t^2))^N / (1+t^2)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)
  have hintf : IntervalIntegrable (fun t => (-(t^2))^N / (1+t^2)) volume 0 u :=
    hcont.intervalIntegrable _ _
  have habs_int : IntervalIntegrable (fun t => |(-(t^2))^N / (1+t^2)|) volume 0 u := hintf.abs
  have hpow_int : IntervalIntegrable (fun t => t^(2*N)) volume 0 u :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h1 : |(∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2))|
      ≤ ∫ t in (0:ℝ)..u, |(-(t^2))^N / (1+t^2)| := by
    have := intervalIntegral.abs_integral_le_integral_abs (f := fun t => (-(t^2))^N / (1+t^2))
      (a := 0) (b := u) (μ := volume) hu
    simpa using this
  have h2 : (∫ t in (0:ℝ)..u, |(-(t^2))^N / (1+t^2)|) ≤ ∫ t in (0:ℝ)..u, t^(2*N) := by
    apply intervalIntegral.integral_mono_on hu habs_int hpow_int
    intro t ht
    have hdenpos : (0:ℝ) < 1 + t^2 := by positivity
    rw [abs_div]
    have hnum : |(-(t^2))^N| = t^(2*N) := by
      rw [abs_pow, abs_neg, abs_of_nonneg (sq_nonneg t), ← pow_mul]
    rw [hnum, abs_of_pos hdenpos]
    have htp : (0:ℝ) ≤ t^(2*N) := by
      rw [pow_mul]; positivity
    apply div_le_self htp (by nlinarith [sq_nonneg t])
  have h3 : (∫ t in (0:ℝ)..u, t^(2*N)) = u^(2*N+1)/(2*N+1) := by
    rw [integral_pow, zero_pow (by omega), sub_zero]; push_cast; ring
  linarith [h1, h2, h3.le, h3.ge]
