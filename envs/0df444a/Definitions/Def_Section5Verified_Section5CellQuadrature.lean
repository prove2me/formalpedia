-- Prove2me | Definitions.Def_Section5Verified_Section5CellQuadrature
-- name    : Section5Verified_Section5CellQuadrature
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:01:12.957613+00:00
-- url     : https://prove2.me/theorems/20825a28-013e-54b7-892b-5b3cd1a92a2d
-- title:
--   Section5CellQuadrature — verified interface
-- statement:
--   Cauchy-Schwarz from a nonnegative square, the cell quadrature bound, its uniform-grid sum, exact floor-rounding cell decomposition, and a position-second-moment tail bound, valid for complex-valued functions.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5CellQuadrature; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

open MeasureTheory Set

noncomputable def section5_grid_sample (a δ x : ℝ) : ℝ :=
  a+δ*(⌊(x-a)/δ⌋ : ℤ)

theorem section5_grid_sample_on_cell (a δ : ℝ) (hδ : 0 < δ) (j : ℕ)
    (x : ℝ) (hx : x ∈ Ico (a+j*δ) (a+(j+1)*δ)) :
    section5_grid_sample a δ x = a+j*δ := by
  have hfloor : ⌊(x-a)/δ⌋ = (j:ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor
    · apply (le_div_iff₀ hδ).mpr
      linarith [hx.1]
    · apply (div_lt_iff₀ hδ).mpr
      linarith [hx.2]
  unfold section5_grid_sample
  rw [hfloor]
  push_cast
  ring

theorem section5_grid_sample_intervalIntegrable {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (a δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    IntervalIntegrable (fun x => ‖f (section5_grid_sample a δ x)‖^2)
      volume a (a+N*δ) := by
  have hcell (j : ℕ) : IntervalIntegrable
      (fun x => ‖f (section5_grid_sample a δ x)‖^2)
      volume (a+j*δ) (a+(j+1)*δ) := by
    apply (intervalIntegrable_const (c := ‖f (a+j*δ)‖^2)).congr_uIoo
    intro x hx
    have hle : a+(j:ℝ)*δ ≤ a+(j+1)*δ := by linarith
    rw [Set.uIoo_of_le hle] at hx
    change ‖f (a+j*δ)‖^2 = ‖f (section5_grid_sample a δ x)‖^2
    rw [section5_grid_sample_on_cell a δ hδ j x ⟨hx.1.le,hx.2⟩]
  have hh := IntervalIntegrable.trans_iterate
    (a := fun j : ℕ => a+j*δ) (n := N)
    (f := fun x => ‖f (section5_grid_sample a δ x)‖^2) (μ := volume)
    (fun j _ => by simpa only [Nat.cast_add,Nat.cast_one] using hcell j)
  simpa only [Nat.cast_zero,zero_mul,add_zero] using hh



/-!
The one-dimensional cell estimate used in Appendix D of the LTF paper. This proof
uses the fundamental theorem of calculus and Cauchy--Schwarz, and is valid for
complex-valued functions (indeed, for any complete real normed space).
-/











end


