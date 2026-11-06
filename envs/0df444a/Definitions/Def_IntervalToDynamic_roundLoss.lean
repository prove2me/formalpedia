-- Prove2me | Definitions.Def_IntervalToDynamic_roundLoss
-- name    : IntervalToDynamic_roundLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:42.158763+00:00
-- url     : https://prove2.me/theorems/481c5944-cbff-4a3e-8dff-d499510aa98c
-- title:
--   Algorithm 1, one round: from $y_t$ to the full loss $h_t$
-- statement:
--   One round of Algorithm 1 as a function of the decision $y=y_t$ of the inner algorithm: play $x_t=\Pi_{\mathcal X}[y_t]$, observe $g_t=\nabla f_t(x_t)$, set $n_t=y_t-x_t$, form the corrected gradient $d_t$, and return the surrogate $h_t$ of Eqs. (10)–(12).
--
--   **Formalization Note** The argument `gr` is the gradient oracle of the round, see `SatisfiesAssumptions`.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Algorithm 1, p.8

import Mathlib
import Definitions.Def_IntervalToDynamic_proj
import Definitions.Def_IntervalToDynamic_correctedGrad
import Definitions.Def_IntervalToDynamic_surrogate

namespace IntervalToDynamic

/-- One round of Algorithm 1 as a function of the decision `y = y_t`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Algorithm 1, p.8: play
`x_t = Π_X[y_t]`, observe `g_t = gr x_t`, set `n_t = y_t − x_t`, form the corrected gradient `d_t`,
and return the full loss `h_t` of Eqs. (10)–(12) fed to the inner algorithm.

**Formalization Note.** `gr` is the gradient oracle of the round: the paper's `∇f_t`, see
`SatisfiesAssumptions`. -/
noncomputable def roundLoss {d : ℕ} (mode : LossMode) (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (gr : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) → ℝ :=
  surrogate mode DX G (correctedGrad (gr (proj X y)) (y - proj X y)) (proj X y) y

end IntervalToDynamic


