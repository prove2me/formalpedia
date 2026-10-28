-- Prove2me | solution 1 for ArctanTaylor.arctan_eq_ps_add_rem
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:30.192016+00:00
-- url     : https://prove2.me/submissions/75dfd09e-ed6a-415a-8098-798b4cb423f0

import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Theorems.Thm_ArctanTaylor_integral_polysum_eq_atanPS

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




theorem solution (u : ℝ) (N : ℕ) :
    arctan u = atanPS u N + ∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2) := by
  have hint : arctan u = ∫ t in (0:ℝ)..u, (1+t^2)⁻¹ := by
    rw [integral_inv_one_add_sq, arctan_zero, sub_zero]
  have hsplit : ∀ t : ℝ, (1+t^2)⁻¹
      = (∑ j ∈ Finset.range N, (-(t^2))^j) + (-(t^2))^N /(1+t^2) := by
    intro t
    have hne : (-(t^2) : ℝ) ≠ 1 := by nlinarith [sq_nonneg t]
    rw [geom_sum_eq hne N]; field_simp; ring
  rw [hint,
    show (∫ t in (0:ℝ)..u, (1+t^2)⁻¹)
      = ∫ t in (0:ℝ)..u, ((∑ j ∈ Finset.range N, (-(t^2))^j) + (-(t^2))^N /(1+t^2)) from by
        apply intervalIntegral.integral_congr; intro t _; exact hsplit t]
  rw [intervalIntegral.integral_add]
  · rw [integral_polysum_eq_atanPS]
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)
