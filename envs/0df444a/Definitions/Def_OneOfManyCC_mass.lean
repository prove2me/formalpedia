-- Prove2me | Definitions.Def_OneOfManyCC_mass
-- name    : OneOfManyCC_mass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:07.222201+00:00
-- url     : https://prove2.me/theorems/66e15a6c-012c-4f95-b0e1-f06a4cb7d074
-- title:
--   Probability of an event under a finite distribution
-- statement:
--   For weights $\mu$ on a finite set $X$ and an event $E\subseteq X$, write
--
--   $$\mu(E)=\sum_{x\in E}\mu(x).$$
--
--   This is $\Pr_{x\sim\mu}[x\in E]$ when $\mu$ is a distribution, as used in the minimax and majority steps and in the inequality $\mu(A')+\nu(B')\ge 1+k^{-2}$.
--
--   **Formalization Note** A distribution is a point of Mathlib's `stdSimplex ℝ X`.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3.3, p.8; §5, pp.10–12

import Mathlib

namespace OneOfManyCC

/-- **The probability of an event under a finite distribution**: `μ(E) = ∑_{x ∈ E} μ(x)`.
Used for the probabilities and the weights `µ(A′)`, `ν(B′)` of
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3.3, p.8 and §5, pp.10–12.

**Formalization Note.** A distribution on a finite set is a point of Mathlib's `stdSimplex ℝ X`
(nonnegative weights summing to `1`). `mass` itself is defined for every weight function. -/
noncomputable def mass {X : Type} [Fintype X] (μ : X → ℝ) (E : Set X) : ℝ :=
  ∑ x, E.indicator μ x

end OneOfManyCC


