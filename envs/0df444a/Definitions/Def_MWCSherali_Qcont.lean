-- Prove2me | Definitions.Def_MWCSherali_Qcont
-- name    : MWCSherali_Qcont
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:57.194443+00:00
-- url     : https://prove2.me/theorems/db072710-d0e0-4cf5-bcdb-358e3234fe98
-- title:
--   The continuous Flow LP value $Q_k$
-- statement:
--   $$Q_k=\inf\sum_{i=1}^kB_i(\Delta_k)$$
--
--   over the feasible solutions of (Continuous-Flow-LP). Theorem 3.4 shows $Q_k=\lim_n q_{k,n}/n$, and Theorem 4.1 gives $Q_4\le2.54492029$.
--
--   **Formalization Note** The infimum is taken in $[0,\infty]$ and so needs no well-definedness lemma (the paper's Lemma 3.3).
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (Continuous-Flow-LP), p.28

import Mathlib
import Definitions.Def_MWCSherali_ContFlowFeasible

namespace MWCSherali

open MeasureTheory
open scoped ENNReal

/-- **The continuous Flow LP value `Q_k`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511
(version of Nov. 3, 2026), (Continuous-Flow-LP), p.28: `Q_k = inf ∑_{i=1}^k B_i(Δ_k)` over the
feasible solutions `(F_{a,i}, B_i, ν_a)`.

**Formalization Note.** The infimum is taken in `ℝ≥0∞`, so it needs no well-definedness lemma
(Lemma 3.3 of the paper shows the feasible set is nonempty; an empty set would give `⊤`). -/
noncomputable def Qcont (k : ℕ) : ℝ≥0∞ :=
  ⨅ (F : Fin k → Fin k → Measure (Fin k → ℝ)) (B : Fin k → Measure (Fin k → ℝ))
    (ν : Fin k → Measure (Fin k → ℝ)) (_ : ContFlowFeasible k F B ν),
    ∑ i, B i (stdSimplex ℝ (Fin k))

end MWCSherali


