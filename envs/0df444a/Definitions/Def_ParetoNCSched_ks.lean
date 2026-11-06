-- Prove2me | Definitions.Def_ParetoNCSched_ks
-- name    : ParetoNCSched_ks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:26.672064+00:00
-- url     : https://prove2.me/theorems/22142541-90c9-47ad-9e5b-0094af70d1dc
-- title:
--   The count $k_s(e)=|\{j: e_j>s\}|$
-- statement:
--   For a vector $e$ and $s\ge0$, $k_s(e)=|\{j:\ e_j>s\}|$ is the number of jobs whose elapsed time exceeds $s$ (that have crossed layer $s$).
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma A.1, p.16

import Mathlib

namespace ParetoNCSched

/-- **The count `k_s(e)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma A.1, p.16: "k_s(e) = |{j : eⱼ > s}| be the number of jobs
whose elapsed time exceeds s". -/
noncomputable def ks {n : ℕ} (e : Fin n → ℝ) (s : ℝ) : ℕ :=
  (Finset.univ.filter fun j => s < e j).card

end ParetoNCSched


