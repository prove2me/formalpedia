-- Prove2me | Definitions.Def_MSetBandit_projObj
-- name    : MSetBandit_projObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:02.424225+00:00
-- url     : https://prove2.me/theorems/4178588b-7930-4fd8-b6d0-666abf28a404
-- title:
--   Projection objective $G_{\tilde\theta}$ of (62)
-- statement:
--   Let $r=m/d$, $\underline\mu_i=\lambda r$ and $\overline\mu_i=1-\lambda(1-r)$ for every $i$. For $\tilde\theta\in\mathbb R^d$, the **projection objective** is
--   $$
--   G_{\tilde\theta}(v)=F(\tilde\theta+v)-\underline\mu^\top v_++\overline\mu^\top v_-,\qquad v\in\mathbb R^d,
--   $$
--   where $F$ is the log-partition function, $(v_+)_i=\max\{v_i,0\}$ and $(v_-)_i=\max\{-v_i,0\}$. Minimizing $G_{\tilde\theta}$ is the dual of the KL projection of $p_{\tilde\theta}$ onto $\mathcal P_\lambda$ (Lemma 7).
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix D.1, Eq. (62), p.33

import Mathlib
import Definitions.Def_MSetBandit_logPartition

namespace MSetBandit

/-- **The projection objective `G_θ̃` of (62).** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Appendix D.1, Eq. (62), p.33:
`G_θ̃(v) := F(θ̃ + v) − µ̲^⊤ v₊ + µ̄^⊤ v₋`, with `µ̲_i := λr`, `µ̄_i := 1 − λ(1 − r)`, `r = m/d`,
`(v₊)_i = max{v_i, 0}`, `(v₋)_i = max{−v_i, 0}`, and `F` the log-partition function.

**Formalization Note.** The text layer prints `µ̲` and `µ̄` alike; the rendered page (and the
derivation on pp.34–35) fixes the lower bound `λr` on the positive part and the upper bound
`1 − λ(1 − r)` on the negative part. -/
noncomputable def projObj {d : ℕ} (m : ℕ) (lam : ℝ) (θt v : Fin d → ℝ) : ℝ :=
  logPartition m (θt + v)
    - ∑ i, lam * ((m : ℝ) / d) * max (v i) 0
    + ∑ i, (1 - lam * (1 - (m : ℝ) / d)) * max (-v i) 0

end MSetBandit


