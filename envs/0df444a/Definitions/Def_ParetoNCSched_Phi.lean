-- Prove2me | Definitions.Def_ParetoNCSched_Phi
-- name    : ParetoNCSched_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:26.022208+00:00
-- url     : https://prove2.me/theorems/c11cc40b-0c48-4284-8594-26bf28faa870
-- title:
--   The frozen-instance optimum $\Phi(e)=\sum_j e_j+\sum_{i<j}\min(e_i,e_j)$
-- statement:
--   For a vector of elapsed times $e=(e_1,\dots,e_n)$ let
--   $$\Phi(e)=\sum_{j} e_j+\sum_{i<j}\min(e_i,e_j).$$
--   The terms $e_j$ are the diagonal terms and the terms $\min(e_i,e_j)$ the pair terms. $\Phi(e)$ is the optimal total completion time of the *frozen instance*, in which job $k$ has size $e_k$; by Smith's rule $\Phi(p)$ is the optimum of the instance with sizes $p$.
--
--   **Formalization Note** Jobs are indexed by `Fin n`; the formula is evaluated on every real vector, the paper uses only nonnegative ones.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.8; Appendix A, Notation, p.15

import Mathlib

namespace ParetoNCSched

/-- **The frozen-instance optimum `Φ`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.8, and Appendix A, Notation, p.15:
"For e ∈ ℝⁿ≥0 let Φ(e) = Σⱼ eⱼ + Σ_{i<j} min(eᵢ, eⱼ)".

**Formalization Note.** Jobs are `Fin n` (0-based); the pair sum ranges over `i < j` in `Fin n`.
`Φ` is defined for every real vector; the paper only evaluates it on nonnegative vectors. -/
noncomputable def Phi {n : ℕ} (e : Fin n → ℝ) : ℝ :=
  ∑ j, e j + ∑ i, ∑ j, if i < j then min (e i) (e j) else 0

end ParetoNCSched


