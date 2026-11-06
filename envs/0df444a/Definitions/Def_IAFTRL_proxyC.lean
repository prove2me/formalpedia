-- Prove2me | Definitions.Def_IAFTRL_proxyC
-- name    : IAFTRL_proxyC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:35.620334+00:00
-- url     : https://prove2.me/theorems/8dbbec84-603f-42f6-a3a0-90971f769a2c
-- title:
--   Proxy stability function $C_t(p)$
-- statement:
--   For round $t\ge1$, a distribution $p$ on $\mathcal A$, the exponential weights $q_t$ and the average action $\bar a_t=\sum_aq_{t,a}a$, the **proxy function** of the stability constraint (2.3f) is
--   $$
--   C_t(p)=\beta_t\sum_{b\in\mathcal A}p_b\sum_{a\in\mathcal A}q_{t,a}\,\chi\!\Big(\frac{(a-\bar a_t)^\top v_b(p)}{\beta_t}\Big),
--   $$
--   with $v_b(p)=M(p)^{-1}b$ and $\chi(x)=e^x+e^{-x}-2$.
--
--   It bounds the conditional expectation of the FTRL mixability gap (Lemma D.4).
--
--   **Formalization Note** This is the computable form of (2.3f) given by the paper itself on p.19. The definition takes the round $t$, the cumulative estimate $S=\sum_{s<t}\hat\theta_s$ (which determines $q_t$) and $p$ as inputs.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.19

import Mathlib
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_chi
import Definitions.Def_IAFTRL_qSoft
import Definitions.Def_IAFTRL_abar
import Definitions.Def_IAFTRL_vCoef

namespace IAFTRL

open Matrix

/-- **The proxy function `C_t(p)`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.19: "because `χ` is even and
increasing in absolute value, the computable form of constraint (2.3f) can be written as
`C_t(p) := β_t Σ_b p_b Σ_a q_{t,a} χ((a − ā_t)^⊤ v_b(p)/β_t) ≤ 2d/β_t`."

`proxyC arms t S p = β_t Σ_b p_b Σ_a q_{t,a} χ((a − ā_t)^⊤ v_b(p) / β_t)`, where `t ≥ 1` is the paper's
round, `β_t = beta d K t`, `q_t = qSoft β_t arms S` with `S = Σ_{s<t} θ̂_s`, and
`ā_t = Σ_a q_{t,a} a`. -/
noncomputable def proxyC {d K : ℕ} (arms : Fin K → Fin d → ℝ) (t : ℕ) (S : Fin d → ℝ)
    (p : Fin K → ℝ) : ℝ :=
  beta d K t * ∑ b, p b * ∑ a, qSoft (beta d K t) arms S a *
    chi (((arms a - abar arms (qSoft (beta d K t) arms S)) ⬝ᵥ vCoef arms p b) / beta d K t)

end IAFTRL


