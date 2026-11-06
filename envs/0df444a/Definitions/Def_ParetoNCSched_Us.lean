-- Prove2me | Definitions.Def_ParetoNCSched_Us
-- name    : ParetoNCSched_Us
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:25:59.168407+00:00
-- url     : https://prove2.me/theorems/e641c537-9c6a-480d-9f89-892eedb97378
-- title:
--   The count $U_s$: unfinished jobs when the level first reaches $s$
-- statement:
--   For a value $s$ that the level $\ell$ reaches, let $t_s$ be the first time with $\ell(t_s)=s$ and $U_s=N(t_s)$ the number of unfinished jobs at that moment. If the level never reaches $s$, $U_s=0$.
--
--   **Formalization Note** $t_s$ is the infimum of the times $t\ge0$ with $\ell(t)=s$, for the level of Lemma D.1.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.1, "The counts U_s", p.21

import Mathlib
import Definitions.Def_ParetoNCSched_levelD

namespace ParetoNCSched

/-- **The count `U_s`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.1, "The counts U_s", p.21: "For a value s that the level
reaches, let t_s be the first time with ℓ(t_s) = s, and let U_s = N(t_s) be the number of unfinished
jobs at that moment. If the level never reaches s, set U_s = 0."

**Formalization Note.** `t_s` is the infimum of the times `t ≥ 0` with `ℓ(t) = s` (the level of
Lemma D.1, `levelD`); `N(t_s)` is the number of unfinished jobs of the run at `t_s`. -/
noncomputable def Us {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (s : ℝ) : ℕ :=
  haveI := Classical.propDecidable (∃ t : ℝ, 0 ≤ t ∧ levelD R p σ t = s)
  if ∃ t : ℝ, 0 ≤ t ∧ levelD R p σ t = s then
    (unfinished p (stateAt R p σ (sInf {t : ℝ | 0 ≤ t ∧ levelD R p σ t = s}))).card
  else 0

end ParetoNCSched


