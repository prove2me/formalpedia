-- Prove2me | Definitions.Def_BewleyGE_savingsCap
-- name    : BewleyGE_savingsCap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:17.266733+00:00
-- url     : https://prove2.me/theorems/3bee053d-8cb5-452b-ae72-e10a4433d047
-- title:
--   Savings cap $\sum_i p_i\bar b/(1-r)^2$
-- statement:
--   At prices $p$ and interest rate $r\in(0,1)$, the **savings cap** is
--   $$
--   \bar s(p,r)=\sum_{i=1}^n\frac{p_i\bar b}{(1-r)^2},
--   $$
--   the largest amount an agent may save. It keeps the state space compact; on normalized prices it tends to infinity as $\sum_ip_i\to0$.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2, pp.5–6

import Mathlib
import Definitions.Def_BewleyGE_Economy

namespace BewleyGE

/-- **Savings cap** `∑ᵢ pᵢ b̄ / (1 − r)²`. Light, arXiv:1906.06810v2, §2, pp.5–6 ("an upper
bound on savings that ensure compactness of the state space where b̄ > 0").

**Formalization Note.** Used only for `0 < r < 1`, where the denominator is positive. -/
noncomputable def savingsCap {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ) : ℝ :=
  (∑ i, p i) * E.bbar / (1 - r) ^ 2

end BewleyGE


