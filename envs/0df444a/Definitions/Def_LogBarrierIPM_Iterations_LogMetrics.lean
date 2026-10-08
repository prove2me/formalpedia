-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_LogMetrics
-- name    : LogBarrierIPM_Iterations_LogMetrics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:45:44.322337+00:00
-- url     : https://prove2.me/theorems/fd58e2cc-0cc2-4c33-8a23-848809779381
-- title:
--   $\log_t$ on $\mathbb R^d_+$, the Funk metric $\delta_F$, the metric $d_\infty$ on $\mathbb T^d$ and the directed Hausdorff distance
-- statement:
--   Fix a base $t$. For $a\ge0$ let $\log_t a=\log a/\log t\in\mathbb T$, with the convention $\log_t 0=-\infty$; for a vector $u\in\mathbb R^d_+$, $\log_t u$ is taken coordinatewise.
--
--   For $x,y\in\mathbb T^d$ the **Funk metric** is
--   $$\delta_F(x,y)=\inf\{\rho\ge0:\ x+\rho e\ge y\}=\max\Big(0,\max_k\,(y_k-x_k)\Big),$$
--   with the convention $-\infty+(+\infty)=-\infty$: a term $y_k-x_k$ is $-\infty$ when $y_k=-\infty$, and $+\infty$ when $y_k$ is finite and $x_k=-\infty$. Its symmetrization is
--   $$d_\infty(x,y)=\max\big(\delta_F(x,y),\delta_F(y,x)\big),$$
--   and for sets $X,Y\subseteq\mathbb T^d$ the **directed Hausdorff distance** is
--   $$d_\infty(X,Y)=\sup_{x\in X}\,\inf_{y\in Y}\,d_\infty(x,y).$$
--   These distances take values in $[0,+\infty]$.
--
--   They measure how far the logarithmic image of a real object is from its tropical counterpart; the paper's estimates (Lemma 8 and later the uniform estimate for the wide neighborhood) are stated with them.
--
--   **Formalization Note** Distances are in `EReal`. The difference term is defined by cases on $-\infty$, which encodes the convention $-\infty+(+\infty)=-\infty$ explicitly instead of relying on `EReal` arithmetic. The directed distance uses `EReal`'s complete-lattice $\sup$/$\inf$; it is $+\infty$ when $X\ne\emptyset$ and $Y=\emptyset$. `logt` sends every non-positive number to $-\infty$; it is only applied to non-negative vectors.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 7 (log_t, log_t 0 = −∞), p. 10 (δ_F), p. 11 (d_∞, directed Hausdorff distance)

import Mathlib

namespace LogBarrierIPM.Iterations

/-- `log_t a ∈ 𝕋 = ℝ ∪ {−∞}` for `a ≥ 0`, with the convention `log_t 0 = −∞` (p. 7).
(Only applied to non-negative reals; a negative argument is also sent to `−∞`.) -/
noncomputable def logt (t a : ℝ) : WithBot ℝ :=
  if 0 < a then ((Real.logb t a : ℝ) : WithBot ℝ) else ⊥

/-- Coordinatewise `log_t` of a vector of `ℝ^d_+`. -/
noncomputable def logtVec {d : ℕ} (t : ℝ) (u : Fin d → ℝ) : Fin d → WithBot ℝ :=
  fun i => logt t (u i)

/-- The difference `b − a ∈ ℝ ∪ {±∞}` of two elements of `𝕋`, with the paper's convention
`−∞ + (+∞) = −∞` (p. 10): it is `−∞` when `b = −∞`, `+∞` when `b` is finite and `a = −∞`. -/
noncomputable def tdiff : WithBot ℝ → WithBot ℝ → EReal
  | ⊥, _ => ⊥
  | (b : ℝ), ⊥ => ⊤
  | (b : ℝ), (a : ℝ) => ((b - a : ℝ) : EReal)

/-- The Funk metric `δ_F(x, y) = inf{ρ ≥ 0 : x + ρe ≥ y} = max(0, max_k (y_k − x_k))` on `𝕋^d`
(p. 10), with `−∞ + (+∞) = −∞`. -/
noncomputable def funk {d : ℕ} (x y : Fin d → WithBot ℝ) : EReal :=
  max 0 (Finset.univ.sup fun k => tdiff (y k) (x k))

/-- `d_∞(x, y) = max(δ_F(x, y), δ_F(y, x))` (p. 11). -/
noncomputable def dInf {d : ℕ} (x y : Fin d → WithBot ℝ) : EReal :=
  max (funk x y) (funk y x)

/-- The directed Hausdorff distance `d_∞(X, Y) = sup_{x ∈ X} inf_{y ∈ Y} d_∞(x, y)` (p. 11). -/
noncomputable def dInfSet {d : ℕ} (X Y : Set (Fin d → WithBot ℝ)) : EReal :=
  ⨆ x ∈ X, ⨅ y ∈ Y, dInf x y

end LogBarrierIPM.Iterations


