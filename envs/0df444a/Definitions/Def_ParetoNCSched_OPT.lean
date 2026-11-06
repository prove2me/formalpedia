-- Prove2me | Definitions.Def_ParetoNCSched_OPT
-- name    : ParetoNCSched_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:46.475482+00:00
-- url     : https://prove2.me/theorems/27a0eaaf-7975-4910-bf21-43e4790aeb45
-- title:
--   The optimum $\mathrm{OPT}(p)$: infimum of $\sum_j C_j$ over all schedules
-- statement:
--   For sizes $p$, $\mathrm{OPT}(p)$ is the optimal total completion time,
--   $$\mathrm{OPT}(p)=\inf\Big\{\sum_j C_j(r):\ r \text{ a schedule}\Big\}\in[0,\infty],$$
--   the infimum over all preemptive single-machine schedules.
--
--   **Formalization Note** $\mathrm{OPT}$ is defined as this infimum, not as $\Phi(p)$; the identity $\mathrm{OPT}(p)=\Phi(p)$ (Smith's rule) is a separate milestone.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_IsSchedule
import Definitions.Def_ParetoNCSched_totalCompletion
open scoped ENNReal

namespace ParetoNCSched

/-- **The optimum `OPT(p)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15: "OPT(p) is its optimal total completion
time". It is the infimum of the total completion time over all preemptive schedules.

**Formalization Note.** OPT is the infimum over **all** schedules in the sense of `IsSchedule`, in
`ℝ≥0∞`; it is not defined as `Φ(p)` (that equality is Smith's rule, a separate statement). -/
noncomputable def OPT {n : ℕ} (p : Fin n → ℝ) : ℝ≥0∞ :=
  ⨅ (r : ℝ → Fin n → ℝ) (_ : IsSchedule r), totalCompletion p r

end ParetoNCSched


