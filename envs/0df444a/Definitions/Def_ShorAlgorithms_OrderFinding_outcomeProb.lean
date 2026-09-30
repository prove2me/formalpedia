-- Prove2me | Definitions.Def_ShorAlgorithms_OrderFinding_outcomeProb
-- name    : ShorAlgorithms_OrderFinding_outcomeProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:07:24.526361+00:00
-- url     : https://prove2.me/theorems/14e3d54b-e33f-480f-b917-60f8020b6c39
-- title:
--   The probability of observing $|c, y\rangle$ in the state (5.4)
-- statement:
--   When a quantum state is measured in the computational basis, the probability of seeing a basis state is the squared modulus of its amplitude. For the final state $\Psi$ of the order-finding algorithm, the probability of observing $|c\rangle$ in the first register and $|y\rangle$ in the second is
--
--   $$
--   P(c, y) = |\Psi(c, y)|^2 .
--   $$
--
--   The probability of an event (a set of outcomes) is the sum of $P$ over it; in particular, the probability of observing a given $c$ in the first register is $\sum_{y} P(c, y)$.
--
--   **Formalization Note** `outcomeProb n x q c y = ‖finalState n x q (c, y)‖ ^ 2`, a real number. No normalization is assumed; that the probabilities sum to $1$ is a consequence of unitarity, not a hypothesis.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1488, §2, "the probability of seeing basis state |S_i⟩ is |a_i|^2"; p. 1499, §5, "Finally, we observe the machine"

import Mathlib
import Definitions.Def_ShorAlgorithms_OrderFinding_finalState

namespace ShorAlgorithms.OrderFinding

/-- Shor (1997), §2, p. 1488 and §5, p. 1499: the probability of observing the basis state
`|c, y⟩` when the final state (5.4) is measured, the squared modulus of its amplitude. -/
noncomputable def outcomeProb (n x q : ℕ) (c : Fin q) (y : ZMod n) : ℝ :=
  ‖finalState n x q (c, y)‖ ^ 2

end ShorAlgorithms.OrderFinding


