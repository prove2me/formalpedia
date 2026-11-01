-- Prove2me | Definitions.Def_PConeEB_zetaBar
-- name    : PConeEB_zetaBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:54.308931+00:00
-- url     : https://prove2.me/theorems/948383d5-b6ac-4723-a844-4fc029f1755b
-- title:
--   The vector $\bar\zeta$ of Lemma 4.1
-- statement:
--   For $q\in(1,\infty)$ and $\zeta\in\mathbb R^n$,
--   $$
--   \bar\zeta:=-\operatorname{sgn}(\zeta)\circ|\zeta|^{q-1},
--   $$
--   where $\circ$ is the Hadamard product, and sgn, the absolute value and the power $q-1$ are taken componentwise.
--
--   When $\|\zeta\|_q=1$, it is the unique minimizer of $\langle\zeta,\omega\rangle$ over the unit $p$-ball.
--
--   **Formalization Note** `Real.sign 0 = 0`.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Lemma 4.1, p.17

import Mathlib

namespace PConeEB

/-- The vector `ζ̄ := -sgn(ζ) ∘ |ζ|^{q-1}` of Lemma 4.1, with sign, absolute value and the power taken
componentwise. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Lemma 4.1, p.17.

**Formalization Note.** `Real.sign 0 = 0`, as in the paper. -/
noncomputable def zetaBar {n : ℕ} (q : ℝ) (ζ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => -Real.sign (ζ i) * |ζ i| ^ (q - 1)

end PConeEB


