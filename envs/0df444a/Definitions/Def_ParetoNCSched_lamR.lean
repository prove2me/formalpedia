-- Prove2me | Definitions.Def_ParetoNCSched_lamR
-- name    : ParetoNCSched_lamR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:27.775676+00:00
-- url     : https://prove2.me/theorems/35412ec5-8963-4edc-9f17-31103143cf12
-- title:
--   The constant $\lambda(R)$ of (16)
-- statement:
--   $$\lambda(R)=R-1-\frac{(R+1)(R-2)}{R}\,K^{\alpha}.$$
--   Lemma D.5(c) shows $\lambda(R)=c(R)-1$.
--
--   **Formalization Note** Named `lamR`.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, Eq. (16), p.28

import Mathlib
import Definitions.Def_ParetoNCSched_KR
import Definitions.Def_ParetoNCSched_alpR

namespace ParetoNCSched

/-- **The constant `λ(R)`** of (16). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, (16), p.28:
"λ(R) = R − 1 − ((R + 1)(R − 2)/R) K^α".

**Formalization Note.** Named `lamR` (`λ` is not an identifier). -/
noncomputable def lamR (R : ℝ) : ℝ :=
  R - 1 - (R + 1) * (R - 2) / R * KR R ^ alpR R

end ParetoNCSched


