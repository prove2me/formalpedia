-- Prove2me | solution 1 for ArctanTaylor.arctan_le_self
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T03:35:41.96793+00:00
-- url     : https://prove2.me/submissions/38db9b1a-93b0-4f09-8930-569b9a8f242c

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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



/-! ### THE INSTRUMENT: the two-sided arctan Taylor bracket. -/



/-! ### Elementary corollaries (no integral) for the far-tail machinery. -/


theorem solution {u : ℝ} (hu : 0 ≤ u) : arctan u ≤ u := by
  set g : ℝ → ℝ := fun y => y - arctan y with hg
  have hderiv : ∀ x, HasDerivAt g (1 - 1/(1+x^2)) x := fun x =>
    (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
  have hmono : Monotone g := by
    apply monotone_of_deriv_nonneg
    · exact fun x => (hderiv x).differentiableAt
    · intro x
      rw [(hderiv x).deriv]
      have hpos : (0:ℝ) < 1 + x^2 := by positivity
      rw [sub_nonneg, div_le_one hpos]; nlinarith [sq_nonneg x]
  have := hmono hu
  simp only [hg, arctan_zero, sub_zero] at this
  linarith
