-- Prove2me | Definitions.Def_SchinzelHypothesisH_core
-- name    : SchinzelHypothesisH_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T02:37:59.715329+00:00
-- url     : https://prove2.me/theorems/2a25baa6-353a-4eef-beb4-275f78b196e1
-- title:
--   Admissibility for Hypothesis H: the Bunyakovsky and Schinzel conditions
-- statement:
--   The three notions Hypothesis H is stated in terms of, for polynomials with integer coefficients.
--
--   **Bunyakovsky condition.** A polynomial $f \in \mathbb{Z}[X]$ satisfies it when its degree is at least $1$, its leading coefficient is positive, and it is irreducible in $\mathbb{Z}[X]$ (irreducibility in $\mathbb{Z}[X]$, not merely in $\mathbb{Q}[X]$, so the content of $f$ is $1$).
--
--   **Schinzel condition.** A finite set $\mathcal{F} \subseteq \mathbb{Z}[X]$ satisfies it when no prime is a fixed divisor of the product: for every prime $p$ there is an integer $n$ with $p \nmid \prod_{f \in \mathcal{F}} f(n)$. For the empty family the product is the empty product $1$, so the condition holds.
--
--   **Prime value set.** For a finite set $\mathcal{F}$, $$S(\mathcal{F}) = \{\, n \in \mathbb{N} : |f(n)| \text{ is a prime number for every } f \in \mathcal{F} \,\},$$ a set of natural numbers; primality is asserted of the absolute value of the integer $f(n)$.
-- source:
--   A. Schinzel, W. Sierpinski, Sur certaines hypotheses concernant les nombres premiers, Acta Arithmetica 4 (1958), 185-208, Hypothesis H (p. 188); https://doi.org/10.4064/aa-4-3-185-208

import Mathlib

namespace SchinzelHypothesisH

open Polynomial

/-- Bunyakovsky's admissibility condition on a single polynomial `f ∈ ℤ[X]`. -/
def BunyakovskyCondition (f : Polynomial ℤ) : Prop :=
  1 ≤ f.natDegree ∧ 0 < f.leadingCoeff ∧ Irreducible f

/-- Schinzel's condition: no prime is a fixed divisor of the product of the family. -/
def SchinzelCondition (fs : Finset (Polynomial ℤ)) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ ((p : ℤ) ∣ ∏ f ∈ fs, f.eval n)

/-- The set of natural numbers at which every member of `fs` takes a value of prime
absolute value. -/
def PrimeValueSet (fs : Finset (Polynomial ℤ)) : Set ℕ :=
  {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}

end SchinzelHypothesisH


