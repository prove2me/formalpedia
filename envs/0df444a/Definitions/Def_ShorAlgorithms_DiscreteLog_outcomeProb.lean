-- Prove2me | Definitions.Def_ShorAlgorithms_DiscreteLog_outcomeProb
-- name    : ShorAlgorithms_DiscreteLog_outcomeProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T00:47:54.356658+00:00
-- url     : https://prove2.me/theorems/93f193e8-a538-490d-8609-baec7745e04b
-- title:
--   Probability of observing $|c,d,y\rangle$ in the state (6.3)
-- statement:
--   With $p,g,x,q$ as in the state (6.1), the **probability of observing** the basis state $|c,d,y\rangle$ ($0\le c,d<q$, $y$ a unit mod $p$) when the final state (6.3) is measured is the squared modulus of its amplitude:
--
--   $$
--   \Pr[c,d,y]=\bigl|\langle c,d,y\mid \text{(6.3)}\rangle\bigr|^2 .
--   $$
--
--   This follows the paper's measurement rule: measuring a superposition $\sum_i a_i|S_i\rangle$ gives $|S_i\rangle$ with probability $|a_i|^2$.
--
--   **Formalization Note** Defined as `‖finalState … (c, d, y)‖ ^ 2`. No normalization hypothesis is assumed; that the probabilities sum to $1$ is a consequence of the construction.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1488, §2 (after eq. (2.1)), and p. 1502, §6 ("Finally, we observe the state")

import Mathlib
import Definitions.Def_ShorAlgorithms_DiscreteLog_finalState

namespace ShorAlgorithms.DiscreteLog

/-- Shor (1997), §2, p. 1488 and §6, p. 1502 ("Finally, we observe the state"): the probability
of observing the basis state `|c, d, y⟩` in `finalState`, the squared modulus of its amplitude. -/
noncomputable def outcomeProb (p : ℕ) (g x : (ZMod p)ˣ) (q : ℕ)
    (c d : Fin q) (y : (ZMod p)ˣ) : ℝ :=
  ‖finalState p g x q (c, d, y)‖ ^ 2

end ShorAlgorithms.DiscreteLog


