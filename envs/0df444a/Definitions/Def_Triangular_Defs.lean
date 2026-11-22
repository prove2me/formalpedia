-- Prove2me | Definitions.Def_Triangular_Defs
-- name    : Triangular_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T18:20:41.287452+00:00
-- url     : https://prove2.me/theorems/6893a543-e901-4550-a8f8-a941bc929040
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Joris Roos's pinned The triangular Hilbert transform and Carleson’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Defs.lean

module
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public noncomputable section
namespace Triangular
open Topology Filter
def T_trunc (F₀ F₁ F₂ : ℝ × ℝ → ℂ) (ε : ℝ) : ℂ :=
  ∫ p in {((x, y), z) : (ℝ × ℝ) × ℝ | ε < |x + y + z|},
    let ((x, y), z) := p
    F₀ (x, y) * F₁ (y, z) * F₂ (z, x) / (x + y + z : ℝ)
def T (F₀ F₁ F₂ : ℝ × ℝ → ℂ) : ℂ := limUnder (𝓝[>] 0) (T_trunc F₀ F₁ F₂)
def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierCoeffOn zero_lt_one f n * fourier n (x : UnitAddCircle)
end Triangular
end


