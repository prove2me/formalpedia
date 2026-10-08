-- Prove2me | Definitions.Def_OrdinaryTwoPointCorrelations
-- name    : OrdinaryTwoPointCorrelations
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:58.990327+00:00
-- url     : https://prove2.me/theorems/f4484424-290a-4c09-adda-26b51ef5d685
-- statement:
--   This block sets up notation for studying two-point correlations of arithmetic functions f, g : ℕ → ℂ. The function liouville(n) is the Liouville function λ(n) viewed as a complex number. correlationSum(f,g,h₁,h₂,N) is the sum over n from 1 to N of f(n+h₁)·g(n+h₂), and affineSum(f,g,a₁,a₂,b₁,b₂,N) is the more general sum over n from 1 to N of f(a₁n+b₁)·g(a₂n+b₂) with natural-number coefficients. Multiplicative(f) means f(mn)=f(m)f(n) whenever m,n are positive and coprime (no normalization such as f(1)=1 is imposed), and OneBounded(f) means |f(n)|≤1 for every positive n. primesUpTo(N) is the set of primes at most N, and squaredDistance(f,g,N) is the pretentious distance squared, the sum over primes p≤N of (1 − Re(f(p)·conj(g(p))))/p. For a Dirichlet character χ modulo q and real t, characterTwist(χ,t)(n) is χ(n mod q)·exp(i t log n). Finally UniformlyNonpretentious(f) is a defined proposition: for every positive modulus q, every Dirichlet character χ mod q and every real K, for all sufficiently large N, every real t with |t|≤N satisfies K ≤ squaredDistance(f, characterTwist(χ,t), N); that is, f stays arbitrarily far from every twisted character in this range. The final namespace OrdinaryTwoPointCorrelations is opened with these definitions but contains no declarations, so no theorem or conjecture is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean; bytes 16..1409
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Filter

namespace TwoPointCorrelations

def liouville (n : ℕ) : ℂ := ArithmeticFunction.liouville n

def correlationSum (f g : ℕ → ℂ) (h₁ h₂ N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, f (n + h₁) * g (n + h₂)

def affineSum (f g : ℕ → ℂ) (a₁ a₂ b₁ b₂ N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, f (a₁ * n + b₁) * g (a₂ * n + b₂)

def Multiplicative (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n

def OneBounded (f : ℕ → ℂ) : Prop := ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1

def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

def squaredDistance (f g : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, (1 - (f p * conj (g p)).re) / (p : ℝ)

def characterTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)

def UniformlyNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℂ q) (K : ℝ),
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, |t| ≤ (N : ℝ) →
      K ≤ squaredDistance f (characterTwist χ t) N

end TwoPointCorrelations

namespace OrdinaryTwoPointCorrelations
open TwoPointCorrelations



end OrdinaryTwoPointCorrelations
end
end OAI


