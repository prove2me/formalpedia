-- Prove2me | Definitions.Def_LimitedBFGS_SQN_sqnIter
-- name    : LimitedBFGS_SQN_sqnIter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:23:41.999002+00:00
-- url     : https://prove2.me/theorems/e749feeb-3f9e-49f8-9b0a-193a3296ec71
-- title:
--   The SQN iteration (17): limited-storage BFGS with exact line searches on a quadratic
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ on $\mathbb{R}^n$, with gradient $g(x) = Ax + b$. Fix an initial matrix $H_0$, a number $m$ of stored corrections and a starting point $x_0$. The **SQN iteration** (Nocedal's (17)) is, for $i = 0, 1, 2, \dots$,
--
--   $$d_i = -H_i g_i, \qquad x_{i+1} = x_i + \alpha_i d_i, \qquad H_{i+1} = F(s_i, y_i, H_i),$$
--
--   where $g_i = g(x_i)$, $\alpha_i$ is the exact line-search step along $d_i$, $s_i = x_{i+1} - x_i$, $y_i = g_{i+1} - g_i$, and $F$ is the special BFGS update (4)–(5): $H_{i+1}$ is $H_0$ updated by the BFGS product form with the $\min(i+1, m)$ most recent pairs $(s_j, y_j)$, oldest first.
--
--   The state of the iteration is the current point $x_i$ together with the list of stored pairs; at each step the new pair $(s_i, y_i)$ is appended and, once more than $m$ pairs are stored, the oldest is discarded. The direction $d_i = -H_i g_i$ is also defined here (`sqnDir`). This is the method known today as L-BFGS.
--
--   **Formalization Note** Indices are 0-based, as in the paper. $H_i$ is rebuilt from $H_0$ and the stored pairs at every step, exactly as (4)–(5) prescribe; it is *not* obtained by one BFGS update of $H_{i-1}$ (that would be ordinary BFGS). There is no stopping rule: once $g_k = 0$, $d_k = 0$, $\alpha_k = 0$, the pair $(0,0)$ is stored (a BFGS step with a zero pair leaves the matrix unchanged), and the iterate remains at the minimizer forever.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 778, eq. (17) ('This algorithm will be called the SQN'); p. 773, definitions of s_k and y_k

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH
import Definitions.Def_LimitedBFGS_SQN_quadratic

open Matrix

namespace LimitedBFGS.SQN

/-- State of the SQN iteration: the current iterate `x` and the stored window of correction
pairs `(s_j, y_j)` (at most `m` of them, oldest first). -/
structure SQNState (n : ℕ) where
  /-- the current iterate `x_k` -/
  x : Fin n → ℝ
  /-- the stored pairs `(s_j, y_j)`, `j = k − min(k, m), …, k − 1`, oldest first -/
  pairs : List ((Fin n → ℝ) × (Fin n → ℝ))

/-- The SQN search direction `d = −H g`, where `H` is the special BFGS matrix (4)–(5) built
from `H₀` and the stored pairs, and `g = A x + b` (Nocedal 1980, p. 778, (17)). -/
noncomputable def sqnDir {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (st : SQNState n) : Fin n → ℝ :=
  -(specialHList H₀ st.pairs *ᵥ grad A b st.x)

/-- The SQN iteration (17) (Nocedal 1980, p. 778) on `f(x) = ½ xᵀAx + bᵀx` with exact line
searches, `m` stored corrections and initial matrix `H₀`, started at `x₀` (0-based):
`d_i = −H_i g_i`, `x_{i+1} = x_i + α_i d_i`, and `H_{i+1} = F(s_i, y_i, H_i)` is the special
BFGS matrix (4)–(5), i.e. `H₀` updated by the last `min(i + 1, m)` pairs
`s_j = x_{j+1} − x_j`, `y_j = g_{j+1} − g_j`. The new pair is appended and the oldest one dropped
once more than `m` are stored. There is no stopping rule: after `g_k = 0`, `d_k = 0`,
`α_k = 0`, the pair `(0, 0)` is stored (a no-op in `bfgsStep`), and the iterate stays put. -/
noncomputable def sqnIter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (x₀ : Fin n → ℝ) : ℕ → SQNState n
  | 0 => ⟨x₀, []⟩
  | k + 1 =>
    let st := sqnIter A b H₀ m x₀ k
    let d := sqnDir A b H₀ st
    let x' := st.x + exactStep A b st.x d • d
    let pairs' := st.pairs ++ [(x' - st.x, grad A b x' - grad A b st.x)]
    ⟨x', pairs'.drop (pairs'.length - m)⟩

end LimitedBFGS.SQN


