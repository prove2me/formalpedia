-- Prove2me | Definitions.Def_MWCSherali_qFlow
-- name    : MWCSherali_qFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:50.761279+00:00
-- url     : https://prove2.me/theorems/8af290d6-a6d1-4c13-876f-7cd2bb379724
-- title:
--   The Flow LP optimum $q_{k,n}$
-- statement:
--   $$q_{k,n}=\min\sum_{x\in\Delta_{k,n}}\sum_{i=1}^kb_{x,i}$$
--
--   over the feasible solutions of (Flow-LP). By Theorem 3.2, $2kn/(kn+q_{k,n})$ is a lower bound for the optimum of (dual-LP$^{\mathrm{no}}_{\mathrm{vertex}}$-w).
--
--   **Formalization Note** The value is an infimum in $[0,\infty]$; an empty feasible set would give $\infty$, not a junk $0$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (Flow-LP), p.23

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_FlowFeasible

namespace MWCSherali

open scoped ENNReal

/-- **The Flow LP optimum `q_{k,n}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511
(version of Nov. 3, 2026), (Flow-LP), p.23: `q_{k,n} = min ∑_{x ∈ Δ_{k,n}} ∑_{i=1}^k b_{x,i}`
over the feasible solutions of (Flow-LP).

**Formalization Note.** The value is an infimum in `ℝ≥0∞` (the objective is nonnegative on the
feasible set, so `ENNReal.ofReal` loses nothing there); an empty feasible set would give `⊤`,
not a junk `0`. -/
noncomputable def qFlow (k n : ℕ) : ℝ≥0∞ :=
  ⨅ (f : Fin k → Grid k n → Fin k → ℝ) (b : Grid k n → Fin k → ℝ) (_ : FlowFeasible k n f b),
    ENNReal.ofReal (∑ x, ∑ i, b x i)

end MWCSherali


