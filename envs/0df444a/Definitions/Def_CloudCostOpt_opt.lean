-- Prove2me | Definitions.Def_CloudCostOpt_opt
-- name    : CloudCostOpt_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:09:49.074052+00:00
-- url     : https://prove2.me/theorems/799e000d-7e2c-4fc8-904b-df22113e2bef
-- title:
--   Optimal value $OPT(\mathbf A,\mathbf B)$
-- statement:
--   For price vectors $\mathbf A,\mathbf B$ and arrival rates $\lambda$,
--
--   $$
--   OPT(\mathbf A,\mathbf B)=\inf_{\pi\in\Pi}f^{\pi}.
--   $$
--
--   The firm's problem (P) is $OPT=OPT(\mathbf R,\mathbf V)$, and the lower bound (P_LB) of §3 is $LB=OPT(\mathbf R,\mathbf R)$: replacing $V_j$ by $R_j$ in $f^\pi$ gives exactly $f^\pi_{LB}$.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.5, (P) and Note; §3, p.11, (P_LB)

import Mathlib
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`OPT(A, B) := inf_{π ∈ Π} f^π`**, the optimal value of `ℙ(A, B)` with arrival rates `lam`.
`OPT = opt S S.R S.V lam` is (ℙ) (p.5) and `LB = opt S S.R S.R lam` is (ℙ_LB) (p.11): replacing `V`
by `R` in `f^π` is exactly `f^π_LB`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.5, (ℙ) and "Note"; §3, p.11, (ℙ_LB). -/
noncomputable def opt (S : System) (A B : Fin S.J → ℝ) (lam : Fin S.I → ℝ≥0) : ℝ≥0∞ :=
  ⨅ (π : Policy S) (_ : IsStable S lam π), avgCost S A B lam π

end CloudCostOpt


