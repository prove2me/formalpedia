-- Prove2me | Definitions.Def_IAFTRL_abar
-- name    : IAFTRL_abar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:55.026256+00:00
-- url     : https://prove2.me/theorems/96b4cb68-053a-4bdb-be5f-d230f87861dc
-- title:
--   FTRL-average action $\bar a_t$
-- statement:
--   For a distribution $q$ on $\mathcal A$, the **average action** is
--   $$
--   \bar a=\sum_{a\in\mathcal A}q_a\,a ;
--   $$
--   with $q=q_t$ it is the paper's $\bar a_t$, used to center the loss-difference estimates in the proxy function $C_t(p)$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.17

import Mathlib

namespace IAFTRL

/-- **The FTRL-average action `ā_t`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.17: "`ā_t = Σ_a q_{t,a} a`".

`abar arms q = Σ_a q_a · arms a`. -/
def abar {d K : ℕ} (arms : Fin K → Fin d → ℝ) (q : Fin K → ℝ) : Fin d → ℝ :=
  ∑ a, q a • arms a

end IAFTRL


