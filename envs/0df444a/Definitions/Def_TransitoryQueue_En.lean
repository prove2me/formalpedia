-- Prove2me | Definitions.Def_TransitoryQueue_En
-- name    : TransitoryQueue_En
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:14.460849+00:00
-- url     : https://prove2.me/theorems/dd06b004-ef5c-4c9e-8b66-6c4d823e7df0
-- title:
--   Fluid time change $E_n(t)$
-- statement:
--   For efficiencies $c_n$, mean service requirement $\mu>0$ and $t\ge0$,
--
--   $$E_n(t)=\frac{c_nt}{n\mu}+p\,r_n(G)+\inf_{0\le s\le t}\Bigl(pG(s)-\frac{c_n}{n}\frac{s}{\mu}\Bigr).$$
--
--   Under Assumption 2.1, $r_n(G)=0$ and this is the paper's first branch; under Assumption 2.5 it is the second. $E_n(t)$ is the fluid limit of the fraction $M_n(D_n(t))/n$ of completed jobs, and $E_n(t)\ge0$.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Theorem 2.11, p.8

import Mathlib
import Definitions.Def_TransitoryQueue_rn

namespace TransitoryQueue

/-- The fluid time change of Theorem 2.11,
`E_n(t) = c_n t/(n μ) + p r_n(G) + inf_{s ≤ t} (p G(s) - (c_n/n)(s/μ))`, the fluid limit of the
fraction `M_n(D_n(t))/n` of completed jobs. Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Theorem 2.11, p.8.

**Formalization Note** One formula for both assumptions: under Assumption 2.1, `F_n = G` and
`r_n = 0`, which is the printed first branch; under Assumption 2.5 it is the printed second
branch. The infimum is over `s ∈ [0, t]`; the function is bounded below there (`G ≥ 0`), so the
real `⨅` is the genuine infimum for `t ≥ 0`. -/
noncomputable def En (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (p μ c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  c * t / (n * μ) + p * rn (F n) G + ⨅ s : Set.Icc (0 : ℝ) t, (p * G s - c / n * (s / μ))

end TransitoryQueue


