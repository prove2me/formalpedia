-- Prove2me | Definitions.Def_MSetBandit_subgradZeta
-- name    : MSetBandit_subgradZeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:10.61821+00:00
-- url     : https://prove2.me/theorems/69209383-1172-43b5-bb2a-3eb077232118
-- title:
--   Subgradient $\zeta(v)$ of (64)
-- statement:
--   Let $r=m/d$, $\underline\mu_i=\lambda r$, $\overline\mu_i=1-\lambda(1-r)$. For $\tilde\theta,v\in\mathbb R^d$ write $\mu=\mu(p_{\tilde\theta+v})$ and define
--   $$
--   \zeta_i(v)=\begin{cases}\mu_i-\underline\mu_i,& v_i>0,\\ \mu_i-\overline\mu_i,& v_i<0,\\ \mu_i-(\underline\mu_i+\overline\mu_i)/2,& v_i=0,\end{cases}\qquad i\in[d].
--   $$
--   By Lemma 7 it is a subgradient of $G_{\tilde\theta}$ at $v$.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Lemma 7, Eq. (64), p.34

import Mathlib
import Definitions.Def_MSetBandit_marg
import Definitions.Def_MSetBandit_wdist

namespace MSetBandit

/-- **The subgradient `ζ(v)` of (64).** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Lemma 7, Eq. (64), p.34: writing
`µ := µ(p_{θ̃+v})`,
`ζ_i(v) := µ_i − µ̲_i` if `v_i > 0`, `µ_i − µ̄_i` if `v_i < 0`, `µ_i − (µ̲_i + µ̄_i)/2` if `v_i = 0`,
with `µ̲_i = λr`, `µ̄_i = 1 − λ(1 − r)`, `r = m/d`. -/
noncomputable def subgradZeta {d : ℕ} (m : ℕ) (lam : ℝ) (θt v : Fin d → ℝ) : Fin d → ℝ :=
  fun i =>
    if 0 < v i then marg (wdist (m := m) (θt + v)) i - lam * ((m : ℝ) / d)
    else if v i < 0 then marg (wdist (m := m) (θt + v)) i - (1 - lam * (1 - (m : ℝ) / d))
    else marg (wdist (m := m) (θt + v)) i - (lam * ((m : ℝ) / d) + (1 - lam * (1 - (m : ℝ) / d))) / 2

end MSetBandit


