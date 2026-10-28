-- Prove2me | solution 1 for ArctanTaylor.integral_polysum_eq_atanPS
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:38:16.771857+00:00
-- url     : https://prove2.me/submissions/c461e998-3402-4575-b7dd-16bfc288daac

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


theorem solution (u : ℝ) (N : ℕ) :
    (∫ t in (0:ℝ)..u, ∑ j ∈ Finset.range N, (-(t^2))^j) = atanPS u N := by
  rw [intervalIntegral.integral_finsetSum]
  · rw [atanPS]
    apply Finset.sum_congr rfl
    intro j _
    have heq : (fun t : ℝ => (-(t^2))^j) = (fun t : ℝ => (-1:ℝ)^j * t^(2*j)) := by
      funext t
      rw [show -(t^2) = (-1:ℝ) * t^2 from by ring, mul_pow, ← pow_mul]
    rw [heq, intervalIntegral.integral_const_mul, integral_pow, zero_pow (by omega), sub_zero]
    have hcast : ((2*j:ℕ):ℝ)+1 = 2*(j:ℝ)+1 := by push_cast; ring
    rw [show (2*j+1 : ℕ) = 2*j+1 from rfl, hcast]
    ring
  · intro j _
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)
