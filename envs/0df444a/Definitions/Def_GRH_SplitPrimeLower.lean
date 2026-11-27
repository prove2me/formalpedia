-- Prove2me | Definitions.Def_GRH_SplitPrimeLower
-- name    : GRH_SplitPrimeLower
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-27T01:44:36.933353+00:00
-- url     : https://prove2.me/theorems/f45c7e12-71fb-485f-9b1b-ad6668a1cdf7
-- title:
--   Primes in the identity class and the regularized Dirichlet product
-- statement:
--   Defines the sum of log p over ordinary primes p ≤ n congruent to 1 modulo q, its prime-power analogue, and a lower bound at square cutoffs. The associated product runs over every Dirichlet character modulo q and removes the principal pole at 1. The cofinal condition uses the factorial levels and exponents of the existing Möbius criterion.
-- source:
--   Arithmetic reduction for GRH.centered_moebius_progression_bilinear_power_bound. The fixed-modulus equivalence is https://prove2.me/theorems/04e865ba-3dd7-43e6-9714-8e4d666e0b7c .

import Definitions.Def_GRH_FactorialMoebius
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Analytic.Order

namespace GRH.SplitPrimeLower
noncomputable section
open Finset
open scoped Classical

/-- Logarithms of ordinary primes in the identity residue class, up to a natural cutoff. -/
def primeWeight (q n : ℕ) : ℝ :=
  ∑ p ∈ Icc 1 n, if p.Prime ∧ (p : ZMod q) = 1 then Real.log p else 0

def mangoldtWeight (q n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod q) k

def squareLower (q : ℕ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
    (u:ℝ)^2 - C * ((u:ℝ)^2 + 1)^θ ≤ (q.totient:ℝ) * primeWeight q (u^2)

def cofinalPrimeLower : Prop :=
  ∀ b : ℕ, ∃ k : ℕ, b ≤ k ∧ squareLower (FactorialMoebius.level k) (FactorialMoebius.exponent k)

def primeMajorant (q : ℕ) (D θ x : ℝ) : ℝ :=
  D * x^θ + (q.totient:ℝ) * mangoldtWeight q ⌊x⌋₊ - x

/-- Product of all Dirichlet L-functions modulo q with the pole at 1 removed. -/
def regularProduct (q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ q s *
    ∏ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), χ.LFunction s

end
end GRH.SplitPrimeLower


