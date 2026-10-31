-- Prove2me | Definitions.Def_TRSHolderKL_fstar
-- name    : TRSHolderKL_fstar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:59.932472+00:00
-- url     : https://prove2.me/theorems/ddeab13d-3747-4fe6-a748-62dff94dafd8
-- title:
--   The optimal value $f^*$ of the TRS
-- statement:
--   The optimal value of the trust region subproblem
--   $$
--   f^*=\min\{f(x): \|x\|\le 1\}.
--   $$
--
--   **Formalization Note** Defined as the infimum of $f$ over the closed unit ball. The ball is compact and nonempty and $f$ is continuous, so the infimum is attained (checked in a verification file); no junk value arises.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, p.1

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
open RBMSensitivity (E)

namespace TRSHolderKL

/-- The optimal value `f*` of (P₀): the infimum of `f` over the unit ball
`B = {x ∈ ℝⁿ | ‖x‖ ≤ 1}`, Jiang and Li, arXiv:1911.11955v2, p.1.

**Formalization Note.** `sInf` of the image of the closed unit ball. The ball is compact and
nonempty and `f` is continuous, so the infimum is attained (checked in the verification
file); no junk value occurs. -/
noncomputable def fstar {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) : ℝ :=
  sInf (f A b '' Metric.closedBall (0 : E n) 1)

end TRSHolderKL


