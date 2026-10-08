-- Prove2me | Definitions.Def_OrdinaryElliott
-- name    : OrdinaryElliott
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:58.802381+00:00
-- url     : https://prove2.me/theorems/862b99f8-3850-4a96-8f48-f0e856dde9da
-- statement:
--   OneBounded(f) says that an arithmetic function f : ℕ → ℂ satisfies |f(n)| ≤ 1 for every n, and Multiplicative(f) says f(mn)=f(m)f(n) whenever m and n are positive coprime integers; it does not require f(1)=1. For a Dirichlet character χ modulo q, a real shift t and a real cutoff X, distanceSq(f,χ,t,X) is the sum over primes p with 2 ≤ p ≤ ⌊X⌋ of (1 − Re(f(p) · conj(χ(p) p^{it}))) / p, where p^{it} is written as exp(i t log p), and distance is its nonnegative square root. This is the pretentious distance between f and the twisted character n ↦ χ(n)n^{it}. UniformlyNonpretentious(f) is the defined property that, for every positive modulus q and every Dirichlet character χ mod q, the infimum of distance(f,χ,t,N) over t in the interval [−N,N] tends to infinity as N → ∞ through the natural numbers, so f stays far from every twisted character, uniformly over shifts of size at most N. Finally, shiftAverage(f₁,f₂,h₁,h₂,N) is the correlation average (1/N) Σ_{n=1}^{N} f₁(n+h₁) f₂(n+h₂) over natural-number shifts h₁ and h₂. No theorem is stated in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OrdinaryElliott.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OrdinaryElliott.lean; bytes 16..1124
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Filter

namespace OrdinaryCorrelations

def OneBounded (f : ℕ → ℂ) : Prop := ∀ n, ‖f n‖ ≤ 1

def Multiplicative (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n

def distanceSq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t X : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊X⌋₊).filter Nat.Prime,
    (1 - (f p * star (χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))).re) / (p : ℝ)

def distance (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t X : ℝ) : ℝ := Real.sqrt (distanceSq f χ t X)

def UniformlyNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ χ : DirichletCharacter ℂ q,
    Tendsto (fun N : ℕ => sInf ((fun t : ℝ => distance f χ t (N : ℝ)) ''
      Set.Icc (-(N : ℝ)) (N : ℝ))) atTop atTop

def shiftAverage (f₁ f₂ : ℕ → ℂ) (h₁ h₂ N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f₁ (n + h₁) * f₂ (n + h₂)



end OrdinaryCorrelations
end
end OAI


