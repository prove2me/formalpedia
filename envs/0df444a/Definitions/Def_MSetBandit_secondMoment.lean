-- Prove2me | Definitions.Def_MSetBandit_secondMoment
-- name    : MSetBandit_secondMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:47.851024+00:00
-- url     : https://prove2.me/theorems/b41b7ad3-3d2b-48f7-94b1-c786e7c2844c
-- title:
--   Second-moment matrix $M(p)$
-- statement:
--   The **second-moment matrix** of $p\in\Delta(\mathcal X)$ is the $d\times d$ matrix
--   $$
--   M(p)=\mathbb E_{X\sim p}[XX^\top],\qquad M(p)_{ij}=\sum_{x\in\mathcal X}p(x)\,x_ix_j .
--   $$
--   When $M(p)$ is invertible, $x^\top M(p)^{-1}x$ is the leverage score of the action $x$ (Eq. (2)).
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.4

import Mathlib
import Definitions.Def_MSetBandit_ind

namespace MSetBandit

/-- **Second-moment matrix `M(p) = E_{X∼p}[X X^⊤]`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, p.4. Entry `(i, j)` is
`Σ_x p(x) x_i x_j`. -/
def secondMoment {d m : ℕ} (p : Action d m → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑ x, p x * (ind x i * ind x j)

end MSetBandit


