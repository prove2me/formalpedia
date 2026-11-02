-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P31
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P31
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:40:28.541375+00:00
-- url     : https://prove2.me/theorems/01861d5f-8a5c-48ec-a890-35f8f862dd02
-- title:
--   Definitions for Entanglement Entropy in the O(N) model
-- statement:
--   The objects the formalized statements of *Entanglement Entropy in the O(N) model* (arXiv:0904.4477) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `transverseHeatTerm`: Summand of the shifted transverse heat trace, PDF p.30, (5.26).
--   - `transverseHeat`: Shifted one-dimensional heat trace, PDF p.30, (5.26). Only positive heat times are used in the statements.
--   - `transverseIntegral`: Heat-kernel continuation of the transverse reciprocal-square sum, PDF p.30, (5.25). Its convergent domain is `2 < D < 4` and nonzero twist.
--   - `squareHeat`: The massless square torus has side `2*pi`. Its heat kernel is defined spectrally, independently of the theta formula; PDF p.27, (5.13)--(5.14).
--   - `OffSquareLattice`: Off the lattice of source points of the side-`2*pi` square torus.
--   - `squareGreen`: Zero-mode-removed inverse Laplacian on the square torus, constructed by the heat kernel. The pointwise integral is used only off its source lattice; its logarithmic singularity is locally integrable. PDF p.27.
--   - `oddThetaAtI`: Odd Jacobi theta function at modulus `i`, with argument of period one, using its convergent sine series, in the convention of PDF p.27, (5.14).
--   - `etaAtI`: Positive real value of Dedekind eta at `i`. Mathlib defines eta by `exp(pi*i*z/12)` times the product of `1-exp(2*pi*i*(j+1)*z)`.
--   - `geometricProfile`: Analytic coefficient profile on the right-hand side of (5.31), PDF p.30. This definition does not assert a physical entropy/partition-function identity; that calculation is the separately deferred node #5.31.
--   - `reducedGap`: The reduced small-alpha gap equation, PDF p.37, (6.33). This is the specified asymptotic truncation, not the full integral gap equation (6.25).
--   - `reducedDiscriminant`: Discriminant in PDF p.37, (6.34).
--   - `reducedRoot`: The two explicit branches of the reduced equation (6.34); `true` selects the plus sign. Negative discriminants are excluded in its use.
--   - `reducedAmplitude`: The retained small-alpha normalization from (6.7) as D tends to four. It is the leading reduced d amplitude, not an exact finite-epsilon value of the original Gamma-normalized saddle. PDF p.37, (6.35).
-- source:
--   Entanglement Entropy in the O(N) model, arXiv:0904.4477v1, https://arxiv.org/abs/0904.4477v1

import Mathlib

/-!
Analytic statements from Metlitski--Fuertes--Sachdev, arXiv:0904.4477v1.
The continuum entropy and interacting-field constructions that are not supplied
here are explicitly deferred in the assigned unit's HARD.md and GAPS.json.
All reduced quantities below are mathematical objects of the indicated
truncation; they are not definitions of the full physical entropy.
-/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P31

/-- Summand of the shifted transverse heat trace, PDF p.30, (5.26). -/
def transverseHeatTerm (s phi : ℝ) (j : ℤ) : ℝ :=
  Real.exp (-s * (2 * Real.pi * (j : ℝ) + phi) ^ 2)

/-- Shifted one-dimensional heat trace, PDF p.30, (5.26).
Only positive heat times are used in the statements. -/
def transverseHeat (s phi : ℝ) : ℝ :=
  ∑' j : ℤ, transverseHeatTerm s phi j

/-- Heat-kernel continuation of the transverse reciprocal-square sum,
PDF p.30, (5.25). Its convergent domain is `2 < D < 4` and nonzero twist. -/
def transverseIntegral (D phi : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), (transverseHeat s phi) ^ (D - 2)

example (s phi : ℝ) : transverseHeatTerm s phi 0 = Real.exp (-s * phi ^ 2) := by
  simp [transverseHeatTerm]

example (s : ℝ) : transverseHeat s 0 =
    ∑' j : ℤ, Real.exp (-s * (2 * Real.pi * (j : ℝ)) ^ 2) := by
  simp [transverseHeat, transverseHeatTerm]

/-- The massless square torus has side `2*pi`. Its heat kernel is defined
spectrally, independently of the theta formula; PDF p.27, (5.13)--(5.14). -/
def squareHeat (s x y : ℝ) : ℝ :=
  (∑' k : ℤ × ℤ,
    Real.exp (-s * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2)) *
      Real.cos ((k.1 : ℝ) * x + (k.2 : ℝ) * y)) / (4 * Real.pi ^ 2)

/-- Off the lattice of source points of the side-`2*pi` square torus. -/
def OffSquareLattice (x y : ℝ) : Prop :=
  ¬ ∃ k : ℤ × ℤ, x = 2 * Real.pi * (k.1 : ℝ) ∧
    y = 2 * Real.pi * (k.2 : ℝ)

/-- Zero-mode-removed inverse Laplacian on the square torus, constructed
by the heat kernel. The pointwise integral is used only off its source
lattice; its logarithmic singularity is locally integrable. PDF p.27. -/
def squareGreen (x y : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), squareHeat s x y - 1 / (4 * Real.pi ^ 2)

/-- Odd Jacobi theta function at modulus `i`, with argument of period one,
using its convergent sine series, in the convention of PDF p.27, (5.14). -/
def oddThetaAtI (z : ℂ) : ℂ :=
  2 * ∑' j : ℕ, (-1 : ℂ) ^ j *
    (Real.exp (-Real.pi * ((j : ℝ) + 1 / 2) ^ 2) : ℂ) *
      Complex.sin (((2 * j + 1 : ℕ) : ℂ) * (Real.pi : ℂ) * z)

/-- Positive real value of Dedekind eta at `i`. Mathlib defines eta by
`exp(pi*i*z/12)` times the product of `1-exp(2*pi*i*(j+1)*z)`. -/
def etaAtI : ℝ := ‖ModularForm.eta Complex.I‖

example : ¬ OffSquareLattice 0 0 := by
  intro h
  exact h ⟨(0, 0), by simp⟩

example : oddThetaAtI 0 = 0 := by
  simp [oddThetaAtI]

example : 0 ≤ etaAtI := by
  exact norm_nonneg _

/-- Analytic coefficient profile on the right-hand side of (5.31), PDF
p.30. This definition does not assert a physical entropy/partition-function
identity; that calculation is the separately deferred node #5.31. -/
def geometricProfile (N : ℕ) (phi : ℝ) : ℝ :=
  Real.pi * (N : ℝ) * squareGreen phi phi / (3 * ((N : ℝ) + 8))

example (phi : ℝ) : geometricProfile 0 phi = 0 := by
  simp [geometricProfile]

/-- The reduced small-alpha gap equation, PDF p.37, (6.33). This is the
specified asymptotic truncation, not the full integral gap equation (6.25). -/
def reducedGap (eps n alpha : ℝ) : ℝ :=
  alpha / n + alpha ^ 2 / eps - (1 / n ^ 2 - 1) / 6

/-- Discriminant in PDF p.37, (6.34). -/
def reducedDiscriminant (eps n : ℝ) : ℝ :=
  eps ^ 2 + (2 / 3 : ℝ) * eps * (1 - n ^ 2)

/-- The two explicit branches of the reduced equation (6.34); `true`
selects the plus sign. Negative discriminants are excluded in its use. -/
def reducedRoot (eps n : ℝ) (plus : Bool) : ℝ :=
  -eps / (2 * n) + (if plus then 1 else -1) *
    Real.sqrt (reducedDiscriminant eps n) / (2 * n)

/-- The retained small-alpha normalization from (6.7) as D tends to four.
It is the leading reduced d amplitude, not an exact finite-epsilon value
of the original Gamma-normalized saddle. PDF p.37, (6.35). -/
def reducedAmplitude (N : ℕ) (eps alpha : ℝ) : ℝ :=
  (N : ℝ) * alpha ^ 2 / (8 * Real.pi ^ 2 * eps)

example (eps n : ℝ) : reducedGap eps n 0 = -(1 / n ^ 2 - 1) / 6 := by
  simp [reducedGap] <;> ring

example (eps : ℝ) : reducedDiscriminant eps 1 = eps ^ 2 := by
  simp [reducedDiscriminant]

example (eps : ℝ) : reducedAmplitude 0 eps 0 = 0 := by
  simp [reducedAmplitude]

end QAlgorithms.Papers.Independent.Intakethird100.P31


