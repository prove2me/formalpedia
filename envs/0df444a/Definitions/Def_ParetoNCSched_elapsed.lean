-- Prove2me | Definitions.Def_ParetoNCSched_elapsed
-- name    : ParetoNCSched_elapsed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:28.765171+00:00
-- url     : https://prove2.me/theorems/ab57d58f-8ba8-4624-b0f2-e3ae4a5b002f
-- title:
--   Elapsed time $e_j(t)=\int_0^t r_j(u)\,du$
-- statement:
--   For a rate function $r$, the *elapsed time* of job $j$ at time $t$ is the processing it has received so far,
--   $$e_j(t)=\int_0^t r_j(u)\,du .$$
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.7; Appendix A, Notation, p.15

import Mathlib

namespace ParetoNCSched

/-- **Elapsed time `eⱼ(t)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.7, and Appendix A, p.15: "eⱼ(t) = ∫₀ᵗ rⱼ(u) du",
the processing job `j` has received by time `t`. -/
noncomputable def elapsed {n : ℕ} (r : ℝ → Fin n → ℝ) (j : Fin n) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, r u j

end ParetoNCSched


