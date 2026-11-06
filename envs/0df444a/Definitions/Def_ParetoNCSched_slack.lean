-- Prove2me | Definitions.Def_ParetoNCSched_slack
-- name    : ParetoNCSched_slack
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:29.703368+00:00
-- url     : https://prove2.me/theorems/fbd2219b-804e-46fd-a014-9d10b5b8513d
-- title:
--   The slack $D=F-R\,\Phi(e)$
-- statement:
--   The *slack* of a state is
--   $$D=F-R\,\Phi(e).$$
--   $\mathrm{MRC}_R$ maintains the robustness invariant $D\le0$, equation (2).
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 3, Eq. (2), p.8; Appendix B, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_MState
import Definitions.Def_ParetoNCSched_Phi

namespace ParetoNCSched

/-- **The slack `D = F − R Φ(e)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 3, (2), p.8, and Appendix B, p.17: "We write
D(t) = F(t) − R Φ(e(t)), the slack". -/
noncomputable def slack {n : ℕ} (R : ℝ) (s : MState n) : ℝ :=
  s.F - R * Phi s.e

end ParetoNCSched


