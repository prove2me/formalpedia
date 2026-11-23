-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
-- name    : GrothendieckLB_Supplement_cqPriceKernels
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T21:15:16.254302+00:00
-- url     : https://prove2.me/theorems/7f7e48e8-b180-4cff-a817-0050e6b00066
-- title:
--   Gaussian and Bell terms for the fifth-order Price expansion
-- statement:
--   The differentiated threshold integrals for the cubic–quintic scheme use a complex bivariate Gaussian density, a one-dimensional Gaussian of variance two, and mixed Fourier moments. The Bell polynomials for the cubic threshold have finitely many integer terms through order five. These definitions specify their coefficients, Gaussian moment bounds, and the resulting twenty spatial integrals explicitly.
-- source:
--   Degree-251 fixed-point Hermite certificate for the cubic–quintic scheme of Saha et al., arXiv:2608.11158v2, and Prove2Me fc28e7f8-2588-498a-8ea6-e8d0e220ae2b.

import Definitions.Def_GrothendieckLB_Supplement_cqPriceMajorant
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MeasureTheory
namespace GrothendieckLB.Supplement.CQPrice

noncomputable def delta : ℝ := 0.136419125 / Real.sqrt (6*(1+0.34101124^2+0.05276111^2))
noncomputable def threshold (x : ℝ) := delta*(x^3-3*x)

/-- The real density with mean zero and variance two. -/
noncomputable def normalTwo (x : ℝ) := Real.exp (-(x^2)/4)/(2*Real.sqrt Real.pi)

/-- The complex bivariate Gaussian density in the sum and difference coordinates. -/
noncomputable def density (z : ℂ) (x y : ℝ) : ℂ :=
  ((1-z^2)^((-(1/2:ℝ):ℝ):ℂ) / ((2*Real.pi:ℝ):ℂ)) *
    Complex.exp (-(((((x+y)^2/4:ℝ):ℂ) * (1+z)⁻¹) + ((((x-y)^2/4:ℝ):ℂ) * (1-z)⁻¹)))

/-- A term in a Bell polynomial for the cubic threshold.
It represents $c x^b(x^2-1)^l$ before the common power of the threshold slope. -/
structure Piece where
  l : ℕ
  b : ℕ
  c : ℕ
  deriving Inhabited

def pieces : ℕ → ℕ → List Piece
  | 0, 0 => [⟨0,0,1⟩]
  | 1, 1 => [⟨1,0,3⟩]
  | 2, 1 => [⟨0,1,6⟩]
  | 2, 2 => [⟨2,0,9⟩]
  | 3, 1 => [⟨0,0,6⟩]
  | 3, 2 => [⟨1,1,54⟩]
  | 3, 3 => [⟨3,0,27⟩]
  | 4, 2 => [⟨0,2,108⟩, ⟨1,0,72⟩]
  | 4, 3 => [⟨2,1,324⟩]
  | 4, 4 => [⟨4,0,81⟩]
  | 5, 2 => [⟨0,1,360⟩]
  | 5, 3 => [⟨1,2,1620⟩, ⟨2,0,540⟩]
  | 5, 4 => [⟨3,1,1620⟩]
  | 5, 5 => [⟨5,0,243⟩]
  | _, _ => []

noncomputable def bell (a i : ℕ) (x : ℝ) := delta^i *
  ((pieces a i).map (fun e => (e.c:ℝ)*x^e.b*(x^2-1)^e.l)).sum

/-- Absolute Bell moment upper endpoints at scale $2^{64}$. -/
def bellUnits : ℕ → ℕ → ℕ
  | 0, 0 => 18446744073709551616
  | 1, 1 => 8740989679327271034
  | 2, 1 => 6584878891759877512
  | 2, 2 => 4141917959549227380
  | 3, 1 => 5827326452884847356
  | 3, 2 => 15601224314302089795
  | 3, 3 => 7777900640339516634
  | 4, 2 => 22090229117595879356
  | 4, 3 => 24642133804440150831
  | 4, 4 => 14524084567936053413
  | 5, 2 => 20801632419069453060
  | 5, 3 => 74144473393890719314
  | 5, 4 => 90559102467303421098
  | 5, 5 => 46169929858444676085
  | _, _ => 0

def momentDF (j : ℕ) := (2*j-1).doubleFactorial
def fourierUnits (m n : ℕ) : ℕ :=
  let a := (2^128 : ℕ)*momentDF m*momentDF n
  let b := Nat.sqrt a
  if b*b=a then b else b+1

/-- The normalized Fourier integral for a mixed shift derivative of the Gaussian density. -/
noncomputable def fourierMoment (q : ℂ) (u v : ℝ) (m n : ℕ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ) * ∫ xy : ℝ × ℝ,
    (Complex.I*(xy.1:ℂ))^m * (Complex.I*(xy.2:ℂ))^n *
      Complex.exp (-(((xy.1:ℂ)^2 + (xy.2:ℂ)^2 + 2*q*xy.1*xy.2)/2) +
        Complex.I*((u:ℂ)*xy.1+(v:ℂ)*xy.2))

/-- Mixed derivative indices with a nonzero Bell factor. -/
def indices (p a : ℕ) : List (ℕ×ℕ) :=
  ((List.range (a+1)).flatMap (fun i => (List.range (a+1)).map (fun j => (i,j)))).filter
    (fun ij => decide (0<bellUnits a ij.1 ∧ 0<bellUnits a ij.2 ∧ 0<p+ij.1 ∧ 0<p+ij.2))

noncomputable def partialTerm (z : ℂ) (p a : ℕ) : ℂ :=
  ∫ xy : ℝ × ℝ, density (-z) xy.1 xy.2 *
    ((indices p a).map (fun ij =>
      ((bell a ij.1 xy.1 * bell a ij.2 xy.2 : ℝ):ℂ) *
        fourierMoment (eval rho z) (threshold xy.1) (threshold xy.2) (p+ij.1-1) (p+ij.2-1))).sum

end GrothendieckLB.Supplement.CQPrice


