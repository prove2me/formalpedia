-- Prove2me | Definitions.Def_ShorAlgorithms_DiscreteLog_preFourierState
-- name    : ShorAlgorithms_DiscreteLog_preFourierState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T00:34:34.910021+00:00
-- url     : https://prove2.me/theorems/0edda80b-de72-4e3e-bc05-ea9e754c451e
-- title:
--   The state (6.1): $\frac1{p-1}\sum_{a,b=0}^{p-2}|a,b,g^ax^{-b}\bmod p\rangle$
-- statement:
--   Let $p$ be a prime, $g,x$ units modulo $p$, and $q$ a positive integer with $p-1<q$. The discrete-logarithm algorithm uses three registers: the first two hold numbers $0\le a,b<q$, and the third holds a nonzero residue modulo $p$. The state prepared before the Fourier transforms is
--
--   $$
--   \frac{1}{p-1}\sum_{a=0}^{p-2}\sum_{b=0}^{p-2}\bigl|a,\;b,\;g^a x^{-b}\ (\mathrm{mod}\ p)\bigr\rangle ,
--   $$
--
--   i.e. the amplitude of $|a,b,y\rangle$ is $1/(p-1)$ if $a,b\le p-2$ and $y=g^ax^{-b}$, and $0$ otherwise.
--
--   This is the input state to which the algorithm applies $A_q$ on the first two registers.
--
--   **Formalization Note** The state is a function `Fin q × Fin q × (ZMod p)ˣ → ℂ`; $x^{-b}$ is `x⁻¹ ^ b` in the unit group; $p-1$ is natural-number subtraction, which is exact because $p\ge2$. The preparation of this state (the page's test-and-restart procedure) is not formalized: the state is taken as displayed in (6.1).
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1502, §6, eq. (6.1)

import Mathlib

namespace ShorAlgorithms.DiscreteLog

/-- Shor (1997), §6, eq. (6.1), p. 1502: the state
`(1/(p-1)) ∑_{a=0}^{p-2} ∑_{b=0}^{p-2} |a, b, g^a x^{-b} (mod p)⟩` of the three registers.
The first two registers have basis `Fin q` (values `0 ≤ a, b < q`) and the state is supported
on `a, b < p - 1`; the third register holds a unit of `ZMod p`, and `x^{-b}` is `x⁻¹ ^ b` in
the unit group. `p - 1` is natural-number subtraction (`p ≥ 2` wherever it is used). -/
noncomputable def preFourierState (p : ℕ) (g x : (ZMod p)ˣ) (q : ℕ) :
    Fin q × Fin q × (ZMod p)ˣ → ℂ :=
  fun s =>
    if (s.1 : ℕ) < p - 1 ∧ (s.2.1 : ℕ) < p - 1 ∧ s.2.2 = g ^ (s.1 : ℕ) * x⁻¹ ^ (s.2.1 : ℕ)
    then (((p - 1 : ℕ) : ℂ))⁻¹ else 0

end ShorAlgorithms.DiscreteLog


