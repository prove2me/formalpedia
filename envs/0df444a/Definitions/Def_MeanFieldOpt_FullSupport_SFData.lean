-- Prove2me | Definitions.Def_MeanFieldOpt_FullSupport_SFData
-- name    : MeanFieldOpt_FullSupport_SFData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:55.199871+00:00
-- url     : https://prove2.me/theorems/7d6af514-449f-4ff0-9a4a-2d4e12eec477
-- title:
--   Non-negative step functions $\mathsf{SF}_+$ (Eq. (6.1))
-- statement:
--   The space of non-negative piecewise constant functions on $[0,1)$ is
--
--   $$
--   \mathsf{SF}_+ = \Bigl\{ g = \sum_{i=1}^m a_i\, \mathbb I_{[t_{i-1}, t_i)} \;:\; 0 = t_0 < t_1 < \dots < t_m = 1,\ a_i \in \mathbb R_{\ge 0},\ m \in \mathbb N \Bigr\}.
--   $$
--
--   An element of $\mathsf{SF}_+$ is given here by its data: the number of pieces $m$, the breakpoints $t_0 < \dots < t_m$ and the values $a_1, \dots, a_m \ge 0$. The associated function is $g(s) = \sum_i a_i \mathbb I(t_{i-1} \le s < t_i)$.
--
--   Step functions are the order parameters for which the Parisi PDE has an explicit Cole–Hopf solution; the solution for a general $\gamma \in \mathscr L$ is obtained from them by continuity.
--
--   **Formalization Note** The pieces are indexed by `Fin m`; piece `i` has value `a i` on `[t i.castSucc, t i.succ)`. Strict monotonicity of the breakpoints with $t_0 = 0$, $t_m = 1$ forces $m \ge 1$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 23, Eq. (6.1)

import Mathlib

namespace MeanFieldOpt.FullSupport

/-- A representation of an element of `SF₊` (arXiv:2001.00904v1, p. 23, Eq. (6.1)):
`g = ∑_{i=1}^m a_i 𝕀_{[t_{i-1}, t_i)}` with `0 = t_0 < t_1 < ⋯ < t_m = 1` and `a_i ≥ 0`.
Piece `i : Fin m` carries the value `a i` on `[t i.castSucc, t i.succ)`. -/
structure SFData where
  m : ℕ
  t : Fin (m + 1) → ℝ
  t_strictMono : StrictMono t
  t_zero : t 0 = 0
  t_last : t (Fin.last m) = 1
  a : Fin m → ℝ
  a_nonneg : ∀ i, 0 ≤ a i

namespace SFData

/-- The step function `∑_i a_i 𝕀_{[t_{i-1}, t_i)}`. -/
noncomputable def toFun (d : SFData) (s : ℝ) : ℝ :=
  ∑ i : Fin d.m, if d.t i.castSucc ≤ s ∧ s < d.t i.succ then d.a i else 0

end SFData

end MeanFieldOpt.FullSupport


