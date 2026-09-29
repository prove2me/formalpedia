-- Prove2me | Definitions.Def_FCP_BatemanHorn
-- name    : FCP_BatemanHorn
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T18:23:41.296069+00:00
-- url     : https://prove2.me/theorems/bab0f70f-dbee-4cab-9c4b-b593780307d9
-- title:
--   Bateman--Horn data: Bunyakovsky and Schinzel conditions, $\omega_p$, the partial Euler product and the counting function
-- statement:
--   This file fixes the data entering the Bateman--Horn conjecture for a finite family $S$ of integer polynomials.
--
--   A single polynomial $f \in \mathbb{Z}[X]$ satisfies the **Bunyakovsky condition** when its leading coefficient is positive, its degree is at least $1$, and it is irreducible in $\mathbb{Z}[X]$.
--
--   A finite family $S$ satisfies the **Schinzel condition** when for every prime $p$ there is an integer $n$ with $p \nmid \prod_{f \in S} f(n)$; this rules out families whose product is divisible by a fixed prime at every integer.
--
--   For a prime $p$, $\omega_p(S)$ is the number of residue classes $n \bmod p$ at which at least one $f \in S$ vanishes, $D(S) = \prod_{f \in S} \deg f$, and the truncated Euler product is
--   $$P_N(S) = \prod_{p < N} \left(1 - \tfrac{1}{p}\right)^{-|S|}\left(1 - \tfrac{\omega_p(S)}{p}\right),$$
--   whose limit as $N \to \infty$ is the Bateman--Horn constant (the product is only conditionally convergent, so the order of the factors matters).
--
--   Finally $\pi_S(x)$ counts the natural numbers $n \le x$ at which every $f \in S$ takes a value of prime absolute value.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/BatemanHornConjecture.lean, Bunyakovsky.lean); https://en.wikipedia.org/wiki/Bateman%E2%80%93Horn_conjecture

import Mathlib

namespace FCP.BatemanHorn

open Polynomial

/-- The Bunyakovsky condition on a single integer polynomial `f`: its leading coefficient is
positive, its degree is at least one, and it is irreducible over `ℤ`. -/
def BunyakovskyCondition (f : ℤ[X]) : Prop :=
  0 < f.leadingCoeff ∧ 1 ≤ f.natDegree ∧ Irreducible f

/-- The Schinzel condition on a finite family of integer polynomials: for every prime `p` there
is an integer `n` with `p ∤ ∏ f ∈ polys, f(n)`. -/
def SchinzelCondition (polys : Finset ℤ[X]) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ ((p : ℤ) ∣ ∏ f ∈ polys, f.eval n)

/-- `omegaP polys p` is the number of residue classes modulo `p` at which at least one of the
polynomials in `polys` vanishes. -/
noncomputable def omegaP (polys : Finset ℤ[X]) (p : ℕ) : ℕ :=
  {n : ZMod p | ∃ f ∈ polys, (f.map (Int.castRingHom (ZMod p))).eval n = 0}.ncard

/-- The product of the degrees of the polynomials in `polys`. -/
def degreesProduct (polys : Finset ℤ[X]) : ℕ := ∏ f ∈ polys, f.natDegree

/-- The partial Euler product defining the Bateman-Horn constant, truncated at the primes `p < N`:
`∏_{p < N} (1 - 1/p)^(-k) (1 - ω_p/p)`, where `k` is the number of polynomials. -/
noncomputable def partialProduct (polys : Finset ℤ[X]) (N : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow N,
    (1 - (1 : ℝ) / p) ^ (-polys.card : ℤ) * (1 - (omegaP polys p : ℝ) / p)

/-- `countSimultaneousPrimes polys x` is the number of natural numbers `n ≤ x` such that every
polynomial in `polys` takes a value of prime absolute value at `n`. -/
noncomputable def countSimultaneousPrimes (polys : Finset ℤ[X]) (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter
    (fun n : ℕ => ∀ f ∈ polys, (f.eval (n : ℤ)).natAbs.Prime)).card

end FCP.BatemanHorn


