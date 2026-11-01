-- Prove2me | Definitions.Def_WassChanceCvx_alphaStar
-- name    : WassChanceCvx_alphaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:58.981927+00:00
-- url     : https://prove2.me/theorems/7708d67e-caad-4a0a-ae77-edda3f9b1244
-- title:
--   The exponent $\alpha^*_n$ of the Borell–Brascamp–Lieb inequality
-- statement:
--   For $n\ge1$ and $\alpha\in[-1/n,+\infty]$,
--
--   $$
--   \alpha^*_n:=\begin{cases}\alpha/(1+n\alpha) & \alpha>-1/n,\ \alpha\ne+\infty,\\ 1/n & \alpha=+\infty,\\ -\infty & \alpha=-1/n.\end{cases}
--   $$
--
--   It is the exponent of the generalized mean in the conclusion of the Borell–Brascamp–Lieb inequality (Proposition 8).
--
--   **Formalization Note** `α` is an extended real; arguments below $-1/n$ are outside the paper's range and give a value no statement uses.
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Proposition 8, p.31

import Mathlib

namespace WassChanceCvx

/-- **The exponent `α*_n` of the Borell–Brascamp–Lieb inequality.**
Shen, Jiang, arXiv:2111.02486v2, Proposition 8, p.31: "`α*_n := α/(1 + nα)` if `α > −1/n`,
`1/n` if `α = +∞`, `−∞` if `α = −1/n`."

`alphaStar n α` is `α*_n`, for `α ∈ [−1/n, +∞]`.

**Formalization Note.** `α` is an extended real. The three branches are tested in the order
`α = +∞`, `α = −1/n`, otherwise (then `α` is a real number `> −1/n` and the value is
`α/(1 + nα)`). Arguments below `−1/n` are outside the paper's range and give a junk value that no
statement uses. -/
noncomputable def alphaStar (n : ℕ) (α : EReal) : EReal :=
  if α = ⊤ then ((1 / (n : ℝ) : ℝ) : EReal)
  else if α = ((-1 / (n : ℝ) : ℝ) : EReal) then ⊥
  else ((α.toReal / (1 + (n : ℝ) * α.toReal) : ℝ) : EReal)

end WassChanceCvx


