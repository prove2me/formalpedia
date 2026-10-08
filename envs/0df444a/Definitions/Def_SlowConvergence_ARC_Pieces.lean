-- Prove2me | Definitions.Def_SlowConvergence_ARC_Pieces
-- name    : SlowConvergence_ARC_Pieces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:42.968523+00:00
-- url     : https://prove2.me/theorems/6642ba71-1e42-4abb-a5de-64a51d64cbc3
-- title:
--   The quintic Hermite pieces $p_k$ of the form (2.11) with the coefficients (5.11) and $\phi_k$
-- statement:
--   With $\eta$ and $s_k$ as in the data of the example, let $\mu = \tfrac23 + 2\eta$ and
--   $$\phi_k = (k+1)^\mu\Big[\Big(\frac1{k+1}\Big)^\mu - \Big(\frac1{k+2}\Big)^\mu\Big] \qquad (k\ge0).$$
--   The $k$-th piece of the example is the quintic polynomial of the form (2.11)
--   $$p_k(t) = c_{0,k} + c_{1,k}t + c_{2,k}t^2 + c_{3,k}t^3 + c_{4,k}t^4 + c_{5,k}t^5$$
--   with
--   $$c_{0,k} = \tfrac23\Big(\frac1{k+1}\Big)^{1+3\eta},\quad c_{1,k} = -\Big(\frac1{k+1}\Big)^{\frac23+2\eta},\quad c_{2,k} = 0,$$
--   and, as in (5.11),
--   $$c_{3,k} = \tfrac{10}3 - 4\phi_k,\qquad c_{4,k} = \frac{-5+7\phi_k}{s_k},\qquad c_{5,k} = \frac{2-3\phi_k}{s_k^2}.$$
--   The paper uses $p_k$ on $[0,s_k]$ and glues the pieces into $f_4(x) = p_k(x-x_k) + f_4(x_{k+1})$ for $x\in[x_k,x_{k+1}]$; the goal theorem does not mention them.
--
--   **Formalization Note** $p_k$ is the polynomial function on all of $\mathbb R$; the interval appears in the milestone statements. The coefficients are stored as a vector indexed by $0,\dots,5$.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 4, (2.11); p. 14, §5, (5.9)–(5.11) and φ_k

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data

namespace SlowConvergence.ARC

/-- The exponent `µ = 2/3 + 2η` of §5, p. 14. -/
noncomputable def mu (τ : ℝ) : ℝ := 2 / 3 + 2 * eta τ

/-- `φ_k = (k+1)^µ [(1/(k+1))^µ − (1/(k+2))^µ]`, §5, p. 14. -/
noncomputable def phi (τ : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) ^ mu τ * ((1 / ((k : ℝ) + 1)) ^ mu τ - (1 / ((k : ℝ) + 2)) ^ mu τ)

/-- The coefficients of the quintic Hermite piece `p_k` of the form (2.11), p. 4, used on `[0, s_k]`
in §5, p. 14: `c_{0,k} = ⅔(1/(k+1))^{1+3η}`, `c_{1,k} = −(1/(k+1))^{2/3+2η}`, `c_{2,k} = 0`, and (5.11)
`c_{3,k} = 10/3 − 4φ_k`, `c_{4,k} = (−5 + 7φ_k)/s_k`, `c_{5,k} = (2 − 3φ_k)/s_k²`. -/
noncomputable def coeff (τ : ℝ) (k : ℕ) : Fin 6 → ℝ :=
  ![2 / 3 * (1 / ((k : ℝ) + 1)) ^ (1 + 3 * eta τ),
    -(1 / ((k : ℝ) + 1)) ^ (2 / 3 + 2 * eta τ),
    0,
    10 / 3 - 4 * phi τ k,
    (-5 + 7 * phi τ k) / sk τ k,
    (2 - 3 * phi τ k) / sk τ k ^ 2]

/-- The quintic Hermite piece (2.11), p. 4, with the coefficients of §5, p. 14:
`p_k(t) = c_{0,k} + c_{1,k} t + c_{2,k} t² + c_{3,k} t³ + c_{4,k} t⁴ + c_{5,k} t⁵`, as a function on
all of `ℝ` (the paper uses it on `[0, s_k]`). -/
noncomputable def p (τ : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  coeff τ k 0 + coeff τ k 1 * t + coeff τ k 2 * t ^ 2 + coeff τ k 3 * t ^ 3 + coeff τ k 4 * t ^ 4
    + coeff τ k 5 * t ^ 5

end SlowConvergence.ARC


