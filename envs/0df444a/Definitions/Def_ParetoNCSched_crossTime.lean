-- Prove2me | Definitions.Def_ParetoNCSched_crossTime
-- name    : ParetoNCSched_crossTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:21:43.974476+00:00
-- url     : https://prove2.me/theorems/a29d3263-6098-4987-9c88-0bc3abae0061
-- title:
--   Crossing time $\tau_i(s)=\inf\{u: e_i(u)>s\}$
-- statement:
--   The time at which job $i$ crosses layer $s$ in the run of $\mathrm{MRC}_R$,
--   $$\tau_i(s)=\inf\{u:\ e_i(u)>s\},$$
--   used for $s\in[0,e_i(t))$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Proof of Lemma D.2, p.22

import Mathlib
import Definitions.Def_ParetoNCSched_mrcRate
import Definitions.Def_ParetoNCSched_elapsed

namespace ParetoNCSched

/-- **The crossing time `τᵢ(s)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), proof of Lemma D.2, p.22: "For s ∈ [0, eᵢ(t)) let
τᵢ(s) = inf{u : eᵢ(u) > s} be the time at which job i crosses layer s". -/
noncomputable def crossTime {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (s : ℝ) : ℝ :=
  sInf {u : ℝ | s < elapsed (mrcRate R p σ) i u}

end ParetoNCSched


