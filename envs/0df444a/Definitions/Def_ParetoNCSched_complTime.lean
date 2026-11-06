-- Prove2me | Definitions.Def_ParetoNCSched_complTime
-- name    : ParetoNCSched_complTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:17.527541+00:00
-- url     : https://prove2.me/theorems/ea04215e-f678-4ee0-978b-36998198ad92
-- title:
--   Completion time $C_j=\inf\{t\ge0: e_j(t)\ge p_j\}$
-- statement:
--   Job $j$ of size $p_j$ completes at the first time its elapsed time reaches its size,
--   $$C_j=\inf\{t\ge 0:\ e_j(t)\ge p_j\}.$$
--
--   **Formalization Note** $C_j$ takes values in $[0,\infty]$: if job $j$ never receives $p_j$ units of processing the infimum of the empty set is $+\infty$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.7; Appendix A, Notation, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_elapsed
open scoped ENNReal

namespace ParetoNCSched

/-- **Completion time `Cⱼ`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.7: "Cⱼ = inf{t ≥ 0 : eⱼ(t) ≥ pⱼ}" (Appendix A,
p.15, writes the same infimum).

**Formalization Note.** Completion times live in `ℝ≥0∞`: the infimum of the empty set is `⊤`, so
a job that never completes has `Cⱼ = ⊤` (never a junk real value). -/
noncomputable def complTime {n : ℕ} (p : Fin n → ℝ) (r : ℝ → Fin n → ℝ) (j : Fin n) : ℝ≥0∞ :=
  ⨅ (t : ℝ) (_ : 0 ≤ t ∧ p j ≤ elapsed r j t), ENNReal.ofReal t

end ParetoNCSched


