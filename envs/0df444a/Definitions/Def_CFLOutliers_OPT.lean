-- Prove2me | Definitions.Def_CFLOutliers_OPT
-- name    : CFLOutliers_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:08.624878+00:00
-- url     : https://prove2.me/theorems/c5aa7f24-e27e-4d05-bd03-c74527dc2038
-- title:
--   Feasible instances and the optimum $\mathrm{OPT}$
-- statement:
--   An instance is **feasible** if it has a capacity-feasible solution serving at least $q$ clients. Its **optimum** is
--
--   $$\mathrm{OPT}=\min\{c(S): S\text{ capacity-feasible},\ |C_S|\ge q\}.$$
--
--   This is the benchmark of Theorem 1.1, Theorem 2.1 and the Appendix B guarantee. With nonnegative costs an optimum serving exactly $q$ clients exists, so the minimum over $|C_S|=q$ is the same number.
--
--   **Formalization Note** The minimum is over a finite nonempty set when the instance is feasible; on an infeasible instance the value is $0$, a junk value, and every statement using $\mathrm{OPT}$ assumes feasibility.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §1 "Problem and result", p.2

import Mathlib
import Definitions.Def_CFLOutliers_Sol

namespace CFLOutliers

open Finset

/-- **Feasible instance**: some capacity-feasible solution serves at least `q` clients.
Dabas, arXiv:2611.04094, §1 "Problem and result", p.2. -/
def Inst.Feasible (I : Inst) : Prop := ∃ S : Sol I, S.CapFeasible ∧ I.q ≤ (served S).card

open Classical in
/-- The capacity-feasible solutions serving at least `q` clients. -/
noncomputable def feasibleSols (I : Inst) : Finset (Sol I) :=
  univ.filter (fun S => S.CapFeasible ∧ I.q ≤ (served S).card)

/-- **The optimum** `OPT` (p.2): the minimum of `c(S)` over capacity-feasible solutions with
`|C_S| ≥ q` ("The objective is to minimize c(S) subject to |C_S| ≥ q").

**Formalization Note.** The minimum is over the finite nonempty set `feasibleSols I` when the
instance is `Feasible`; the value `0` on an infeasible instance is a junk value, and every
statement using `OPT` assumes `Inst.Feasible`. -/
noncomputable def OPT (I : Inst) : ℝ :=
  if h : (feasibleSols I).Nonempty then (feasibleSols I).inf' h cost else 0

end CFLOutliers


