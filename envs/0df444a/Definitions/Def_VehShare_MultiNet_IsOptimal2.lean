-- Prove2me | Definitions.Def_VehShare_MultiNet_IsOptimal2
-- name    : VehShare_MultiNet_IsOptimal2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:43:28.481073+00:00
-- url     : https://prove2.me/theorems/14403bf8-8822-4cdc-9f07-926e3a4afafa
-- title:
--   Optimal solutions $q^s$ of Problem (2)
-- statement:
--   $q^s$ is **optimal for Problem (2)** with budget $\Delta$ if it is feasible and $R_s(q)\le R_s(q^s)$ for every feasible $q$. The paper takes $\Delta\ge K$ (p. 6); that hypothesis is stated on the theorems, not in this predicate.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, Problem (2), pp. 5–6

import Mathlib
import Definitions.Def_VehShare_MultiNet_IsFeasible2
import Definitions.Def_VehShare_MultiNet_Rs

namespace VehShare.MultiNet

/-- **Optimal solutions `q^s` of Problem (2).**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), Problem (2), p. 5, and p. 6 ("where `Δ ≥ K`"): `q^s` maximizes `R_s` over the feasible set.

**Formalization Note.** The standing assumption `Δ ≥ K` is a hypothesis of the theorems that use
it, not part of this predicate. -/
def IsOptimal2 (P : Instance) (Δ : ℝ) (q : P.L → P.L → ℝ) : Prop :=
  IsFeasible2 P Δ q ∧ ∀ q', IsFeasible2 P Δ q' → Rs P q' ≤ Rs P q

end VehShare.MultiNet


