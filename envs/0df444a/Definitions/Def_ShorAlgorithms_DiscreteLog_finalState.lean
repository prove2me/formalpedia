-- Prove2me | Definitions.Def_ShorAlgorithms_DiscreteLog_finalState
-- name    : ShorAlgorithms_DiscreteLog_finalState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T00:41:10.850981+00:00
-- url     : https://prove2.me/theorems/ca31d8fe-a5ba-4146-8327-8ce3b8e3af05
-- title:
--   The state (6.3): $A_q\otimes A_q$ applied to the first two registers of (6.1)
-- statement:
--   With $p,g,x,q$ as in the state (6.1), the **final state** of the discrete-logarithm algorithm is obtained from (6.1) by applying the Fourier matrix $A_q$ to the first register and $A_q$ to the second register, leaving the third register unchanged. Its amplitude at the basis state $|c,d,y\rangle$ ($0\le c,d<q$, $y$ a unit mod $p$) is
--
--   $$
--   \sum_{a=0}^{q-1}\sum_{b=0}^{q-1}\psi(a,b,y)\,(A_q)_{a,c}\,(A_q)_{b,d},
--   $$
--
--   where $\psi$ is the state (6.1). Since $(A_q)_{a,c}(A_q)_{b,d}=\frac1q\exp\bigl(\frac{2\pi i}{q}(ac+bd)\bigr)$, this is the state
--
--   $$
--   \frac{1}{(p-1)q}\sum_{a,b=0}^{p-2}\sum_{c,d=0}^{q-1}\exp\!\left(\frac{2\pi i}{q}(ac+bd)\right)|c,d,g^ax^{-b}\ (\mathrm{mod}\ p)\rangle
--   $$
--
--   displayed on the page.
--
--   **Formalization Note** The state is *defined* as the Fourier transforms applied to (6.1), not typed in as the closed form; the closed form and the observation probabilities derived from it are theorems.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1502, §6, eqs. (6.2)–(6.3)

import Mathlib
import Definitions.Def_ShorAlgorithms_Shared_fourierMatrix
import Definitions.Def_ShorAlgorithms_DiscreteLog_preFourierState

namespace ShorAlgorithms.DiscreteLog

/-- Shor (1997), §6, eqs. (6.2)–(6.3), p. 1502: the state after applying the Fourier transform
`A_q` to each of the first two registers of the state (6.1) (`preFourierState`), leaving the
third register alone. With the row = input convention of §2, the amplitude at `|c, d, y⟩` is
`∑_{a,b} ψ(a, b, y) A_q(a, c) A_q(b, d)`. This is (6.3) by construction. -/
noncomputable def finalState (p : ℕ) (g x : (ZMod p)ˣ) (q : ℕ) :
    Fin q × Fin q × (ZMod p)ˣ → ℂ :=
  fun s => ∑ a : Fin q, ∑ b : Fin q,
    preFourierState p g x q (a, b, s.2.2) * ShorAlgorithms.Shared.fourierMatrix q a s.1 *
      ShorAlgorithms.Shared.fourierMatrix q b s.2.1

end ShorAlgorithms.DiscreteLog


