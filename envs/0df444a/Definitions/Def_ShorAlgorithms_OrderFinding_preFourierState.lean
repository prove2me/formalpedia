-- Prove2me | Definitions.Def_ShorAlgorithms_OrderFinding_preFourierState
-- name    : ShorAlgorithms_OrderFinding_preFourierState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T08:58:56.740239+00:00
-- url     : https://prove2.me/theorems/61b3c9c7-602c-4c05-a537-03ce46e3bb4b
-- title:
--   The state (5.2): $q^{-1/2}\sum_{a=0}^{q-1}|a\rangle|x^a \bmod n\rangle$
-- statement:
--   Fix integers $n$, $x$ and $q$. The order-finding algorithm uses two registers: the first holds a number $0 \le a < q$, the second a residue modulo $n$. After the first register is placed in uniform superposition and $x^a \bmod n$ is computed into the second register, the machine is in the state
--
--   $$
--   \psi = \frac{1}{q^{1/2}} \sum_{a=0}^{q-1} |a\rangle\,|x^a \bmod n\rangle .
--   $$
--
--   Its amplitude on the basis state $|a, y\rangle$ is $q^{-1/2}$ when $y \equiv x^a \pmod n$ and $0$ otherwise.
--
--   This is the input to the Fourier transform step of the algorithm.
--
--   **Formalization Note** A state is a function `Fin q × ZMod n → ℂ`; the second register is `ZMod n`. The amplitude is `if (x : ZMod n) ^ a = y then ((Real.sqrt q : ℝ) : ℂ)⁻¹ else 0`.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1499, §5, eq. (5.2)

import Mathlib

namespace ShorAlgorithms.OrderFinding

/-- Shor (1997), §5, eq. (5.2), p. 1499: the state
`q^{-1/2} ∑_{a=0}^{q-1} |a⟩ |x^a (mod n)⟩` of the two registers after modular exponentiation.
The first register holds `a ∈ {0, …, q-1}` (`Fin q`), the second a residue mod `n` (`ZMod n`).
The amplitude of the basis state `|a, y⟩` is `q^{-1/2}` if `y = x^a (mod n)` and `0` otherwise. -/
noncomputable def preFourierState (n x q : ℕ) : Fin q × ZMod n → ℂ :=
  fun p => if ((x : ZMod n) ^ (p.1 : ℕ) = p.2) then ((Real.sqrt q : ℝ) : ℂ)⁻¹ else 0

end ShorAlgorithms.OrderFinding


