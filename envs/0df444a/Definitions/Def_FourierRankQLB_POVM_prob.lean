-- Prove2me | Definitions.Def_FourierRankQLB_POVM_prob
-- name    : FourierRankQLB_POVM_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:27.795197+00:00
-- url     : https://prove2.me/theorems/d7d96948-17ad-435e-aa02-516817c9b48f
-- title:
--   The outcome probability $\langle\psi,E(S)\psi\rangle$
-- statement:
--   For a POVM $E$, a state $\psi$ and a measurable set of outcomes $S$, the probability
--   $$
--   \langle\psi,E(S)\psi\rangle .
--   $$
--   Its value lies in $[0,1]$ at a unit vector, and the probabilities of $S$ and its complement add up to one.
--
--   **Formalization Note** The real part of the inner product is taken, which is the inner product itself for a positive effect.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §3.1, p.18

import Mathlib
import Definitions.Def_FourierRankQLB_POVM

namespace FourierRankQLB

/-- The probability `⟨ψ, E(S) ψ⟩` of the outcome set `S` at a state `ψ`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §3.1, p. 18.

**Formalization Note.** The inner product is real for a positive effect; its real part is taken so
that the value is a real number. -/
noncomputable def POVM.prob {X H : Type} [MeasurableSpace X] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (M : POVM X H) (ψ : H) (S : Set X) : ℝ :=
  (inner ℂ ψ (M.eff S ψ)).re

end FourierRankQLB


