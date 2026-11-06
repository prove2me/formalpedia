-- Prove2me | Definitions.Def_ParetoNCSched_ns
-- name    : ParetoNCSched_ns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:27.256235+00:00
-- url     : https://prove2.me/theorems/90bc39b3-5af0-4e64-8b9f-8eb39ba69b38
-- title:
--   The count $n_s=|\{i: p_i>s\}|$
-- statement:
--   For $s\ge0$, $n_s=|\{i:\ p_i>s\}|$ is the number of jobs of size larger than $s$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.1, p.20

import Mathlib

namespace ParetoNCSched

/-- **The count `n_s`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.1, p.20: "n_s = |{i : pᵢ > s}| be the number of jobs of
size > s". -/
noncomputable def ns {n : ℕ} (p : Fin n → ℝ) (s : ℝ) : ℕ :=
  (Finset.univ.filter fun i => s < p i).card

end ParetoNCSched


