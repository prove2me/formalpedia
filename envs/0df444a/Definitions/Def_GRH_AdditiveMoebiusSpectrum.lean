-- Prove2me | Definitions.Def_GRH_AdditiveMoebiusSpectrum
-- name    : GRH_AdditiveMoebiusSpectrum
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-27T05:10:36.694152+00:00
-- url     : https://prove2.me/theorems/a8cb25d0-e507-45c7-b652-1b32c2898fab
-- title:
--   Finite rational spectra of the ordinary and centered Möbius weights
-- statement:
--   For a cutoff N, the unsigned weight is μ(n). The signed weight changes sign for n above the integer square root of N. Define the residues, reciprocal correction, rational Fourier transforms, finite Farey sets, exceptional frequencies and residue-row variance.
-- source:
--   Möbius bilinear progression problem on Prove2Me. The finite sums and all normalizations use the original GRH_MoebiusBilinear definition. The Fourier character is Mathlib’s ZMod.stdAddChar.

import Definitions.Def_GRH_OneSidedMoebius
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.Round

namespace GRH.AdditiveMoebiusSpectrum

open Finset
noncomputable section

/-- The signed version changes the sign of the ordinary Möbius weights after the square root. -/
def weight (signed : Bool) (N n : ℕ) : ℝ :=
  if signed = true ∧ N.sqrt < n then -(ArithmeticFunction.moebius n : ℝ)
  else (ArithmeticFunction.moebius n : ℝ)

def fiber {q : ℕ} (a : ZMod q) (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range (N+1), if (n : ZMod q) = a then w n else 0

def correction (q : ℕ) [NeZero q] (N : ℕ) : ℝ :=
  (N : ℝ) / q * (GRH.reducedMoebiusHarmonic q N.sqrt)^2

def angle {q : ℕ} (h : ZMod q) : ℚ := (h.val : ℚ) / q

def transform (signed : Bool) (N : ℕ) (x : ℚ) : ℂ :=
  ∑ n ∈ range (N+1), (weight signed N n : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * ((n : ℝ) * (x : ℝ)))

def exceptional (signed : Bool) (N : ℕ) (A : Finset ℚ) (T : ℝ) : Finset ℚ :=
  A.filter fun x => T < ‖transform signed N x‖

/-- All reduced rational frequencies in the half-open unit interval with denominator at most Q. -/
def fareySet (Q : ℕ) : Finset ℚ :=
  (((range Q) ×ˢ (Icc 1 Q)).image (fun p : ℕ × ℕ => (p.1 : ℚ)/p.2)).filter
    fun x => 0 ≤ x ∧ x < 1 ∧ x.den ≤ Q

def rowVariance (q N : ℕ) [NeZero q] : ℝ :=
  let B := fun a : ZMod q => GRH.centeredMoebiusBilinear q a N
  ∑ a : ZMod q, (B a - (∑ b : ZMod q, B b)/(q : ℝ))^2

def primeVariance (p : Nat.Primes) (N : ℕ) : ℝ :=
  haveI : NeZero p.val := ⟨p.property.ne_zero⟩
  rowVariance p.val N

def escapes : Prop :=
  ∀ x : ℚ, 0 ≤ x → x < 1 → ∀ θ : ℝ, 1/2 < θ → θ < 1 →
    ∃ U : ℕ, ∀ u : ℕ, U ≤ u →
      ‖transform false (u^2) x‖ ≤ ((u : ℝ)^2+1)^θ

end
end GRH.AdditiveMoebiusSpectrum


