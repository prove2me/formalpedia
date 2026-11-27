-- Prove2me | Definitions.Def_GRH_SquarefullFrequencies
-- name    : GRH_SquarefullFrequencies
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-27T06:02:50.562913+00:00
-- url     : https://prove2.me/theorems/32852133-9b37-4033-8bd6-e19a299c869a
-- title:
--   Squarefull denominators and a modulus-one comparison for Möbius sums
-- statement:
--   Finite rational-frequency shifts, power bounds for primitive frequencies with a fixed denominator, and the square-cutoff condition on squarefull denominators. A positive squarefull integer has every prime divisor with multiplicity at least two. The residue variance and exceptional count compare each actual prime-modulus bilinear sum with the modulus-one sum divided by the prime.
-- source:
--   For the Möbius function, write S_N(x) for the sum of μ(n) exp(2πinx) through N. The bilinear sum B(q,a,N) and the coprime reciprocal sum H_q(U) use the original mission normalizations.

import Definitions.Def_GRH_AdditiveMoebiusSpectrum

namespace GRH.SquarefullFrequencies
open Finset AdditiveMoebiusSpectrum
noncomputable section

def phase (n : ℕ) (x : ℚ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((n : ℝ) * (x : ℝ)))

def shifts (d N : ℕ) (x : ℚ) : ℂ :=
  ∑ j ∈ range d, transform false N (x + (j : ℚ)/d)

def primeSquareShifts (p N : ℕ) (x : ℚ) : ℂ :=
  ∑ j ∈ (range (p^2)).filter (fun j => ¬ p ∣ j), transform false N (x + (j : ℚ)/(p:ℚ)^2)

/-- Every prime divisor occurs with exponent at least two. -/
def squarefull (q : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ q → p^2 ∣ q

def boundAt (x : ℚ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖transform false N x‖ ≤ C*((N : ℝ)+1)^θ

def level (q : ℕ) (θ : ℝ) : Prop :=
  ∀ a : ℕ, a.Coprime q → boundAt ((a : ℚ)/q) θ

def squarefullTests : Prop :=
  ∀ q : ℕ, 0 < q → squarefull q → ∀ a : ℕ, a < q → a.Coprime q →
    ∀ θ : ℝ, 1/2 < θ → θ < 1 → ∃ U : ℕ, ∀ u : ℕ, U ≤ u →
      ‖transform false (u^2) ((a : ℚ)/q)‖ ≤ ((u : ℝ)^2+1)^θ

def primeHarmonic (p : Nat.Primes) (U : ℕ) : ℝ :=
  haveI : NeZero p.val := ⟨p.property.ne_zero⟩
  GRH.reducedMoebiusHarmonic p.val U

def relativeVariance (p : Nat.Primes) (N : ℕ) : ℝ :=
  haveI : NeZero p.val := ⟨p.property.ne_zero⟩
  ∑ a : ZMod p.val, (GRH.centeredMoebiusBilinear p.val a N -
    GRH.centeredMoebiusBilinear 1 0 N/(p.val : ℝ))^2

def exceptionalResidues (p : Nat.Primes) (N : ℕ) (T : ℝ) : ℕ :=
  haveI : NeZero p.val := ⟨p.property.ne_zero⟩
  ((univ : Finset (ZMod p.val)).filter fun a => T <
    |GRH.centeredMoebiusBilinear p.val a N-GRH.centeredMoebiusBilinear 1 0 N/(p.val : ℝ)|).card

end
end GRH.SquarefullFrequencies


