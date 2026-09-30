-- Prove2me | Definitions.Def_ShorAlgorithms_OrderFinding_finalState
-- name    : ShorAlgorithms_OrderFinding_finalState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:02:32.946139+00:00
-- url     : https://prove2.me/theorems/1cd03267-6652-4542-ac10-59dd15433cd6
-- title:
--   The state (5.4): $A_q$ applied to the first register of (5.2)
-- statement:
--   Let $\psi$ be the state (5.2) on the two registers and $A_q$ the Fourier matrix. Applying $A_q$ to the first register only, and leaving the second register alone, gives the state $\Psi$ with amplitudes
--
--   $$
--   \Psi(c, y) = \sum_{a=0}^{q-1} \psi(a, y)\,(A_q)_{a,c}, \qquad 0 \le c < q,\ y \in \mathbb{Z}/n .
--   $$
--
--   Written out, this is the paper's state (5.4),
--
--   $$
--   \frac{1}{q} \sum_{a=0}^{q-1} \sum_{c=0}^{q-1} \exp(2\pi i a c / q)\, |c\rangle\, |x^a \bmod n\rangle .
--   $$
--
--   Measuring this state is the quantum part of the order-finding algorithm.
--
--   **Formalization Note** The state is built from its parts: it is the matrix $A_q \otimes I$ applied to (5.2) with the row = input convention (output amplitude at `(c, y)` is `∑ a, ψ (a, y) * A_q a c`), written as that sum directly. The closed form (5.4) is not typed in, so the probability formulas (5.5)–(5.6) are theorems about this construction, not definitions.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1499, §5, eqs. (5.3)–(5.4)

import Mathlib
import Definitions.Def_ShorAlgorithms_Shared_fourierMatrix
import Definitions.Def_ShorAlgorithms_OrderFinding_preFourierState

namespace ShorAlgorithms.OrderFinding

/-- Shor (1997), §5, eqs. (5.3)–(5.4), p. 1499: the state obtained from (5.2) by applying the
Fourier transform `A_q` to the first register only (`A_q ⊗ 1`). With the row = input
convention, the amplitude of `|c, y⟩` is `∑_a ψ(a, y) · (A_q)_{a,c}`, where `ψ` is the state
(5.2). This is (5.4) by construction; its closed form is not typed in. -/
noncomputable def finalState (n x q : ℕ) : Fin q × ZMod n → ℂ :=
  fun p => ∑ a : Fin q,
    preFourierState n x q (a, p.2) * ShorAlgorithms.Shared.fourierMatrix q a p.1

end ShorAlgorithms.OrderFinding


