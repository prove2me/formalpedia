-- Prove2me | Definitions.Def_SteuerChoo_Lexico_tcheb
-- name    : SteuerChoo_Lexico_tcheb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:50:01.448635+00:00
-- url     : https://prove2.me/theorems/b2c45f69-b15e-473b-afa5-91d49520395f
-- title:
--   Optimal value $\max_i \lambda_i(z^*_i - z_i)$ of the weighted Tchebycheff program at a criterion vector
-- statement:
--   Let $\lambda\in\mathbb R^k$ be a weight vector and $z^*\in\mathbb R^k$ the ideal criterion vector. The **weighted Tchebycheff program**
--   $$
--   \min\ \alpha\quad\text{s.t.}\quad \alpha\ge\lambda_i(z^*_i-z_i),\ 1\le i\le k,\qquad z\in Z,
--   $$
--   has, for a fixed criterion vector $z$, the smallest feasible $\alpha$ equal to
--   $$
--   t_\lambda(z)=\max_{1\le i\le k}\lambda_i\,(z^*_i-z_i).
--   $$
--   So a criterion vector minimizes the weighted Tchebycheff program exactly when it minimizes $t_\lambda$ over $Z$.
--
--   This is the first-stage objective of the lexicographic weighted Tchebycheff program.
--
--   **Formalization Note** The auxiliary variable $\alpha$ of the program is eliminated by this value, and the constraints $f_i(x)=z_i$, $x\in S$ are replaced by $z\in Z$. The maximum is `Finset.sup'` over the $k\ge1$ objectives (`[NeZero k]`). The paper's metric $\max_i\lambda_i|z^*_i-z_i|$ agrees with this value on $Z$ because $z\le z^*$ there; the program form, without absolute values, is the one used.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983), p. 330, §3, the weighted Tchebycheff program

import Mathlib

namespace SteuerChoo.Lexico

/-- The minimal value of `α` in the weighted Tchebycheff program at the
criterion vector `z` (§3, p. 330): `max_i λ_i (z*_i − z_i)`, the least `α`
satisfying `α ≥ λ_i (z*_i − z_i)` for `1 ≤ i ≤ k`. -/
noncomputable def tcheb {k : ℕ} [NeZero k] (lam zstar z : Fin k → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => lam i * (zstar i - z i))

end SteuerChoo.Lexico


