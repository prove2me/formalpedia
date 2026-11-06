-- Prove2me | Definitions.Def_ParetoNCSched_costSoFar
-- name    : ParetoNCSched_costSoFar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:23.875129+00:00
-- url     : https://prove2.me/theorems/0b4b80c2-113d-4eb0-8dae-467e6a36d9e3
-- title:
--   Cost so far $F(t)=\int_0^t N(u)\,du$
-- statement:
--   The *cost paid so far* at time $t$ is
--   $$F(t)=\int_0^t N(u)\,du ,$$
--   since the total completion time grows at rate $N(t)$; at the end $F(\infty)=\sum_j C_j$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.7; Appendix A, Notation, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_numUnfinished

namespace ParetoNCSched

/-- **The cost so far `F(t)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.7, and Appendix A, p.15: "F(t) = ∫₀ᵗ N(u) du". -/
noncomputable def costSoFar {n : ℕ} (p : Fin n → ℝ) (r : ℝ → Fin n → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, (numUnfinished p r u : ℝ)

end ParetoNCSched


