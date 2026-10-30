-- Prove2me | Definitions.Def_VehShare_SeqBounds_IsOptimal2
-- name    : VehShare_SeqBounds_IsOptimal2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:41:18.381696+00:00
-- url     : https://prove2.me/theorems/75326473-2775-476c-b42f-63df776643e5
-- title:
--   Optimal solutions $q^s$ of Problem (2)
-- statement:
--   $q^s$ is **optimal for Problem (2)** with budget $\Delta$ if it is feasible and $R_s(q)\le R_s(q^s)$ for every feasible $q$. The paper takes $\Delta\ge K$ (p. 6); that hypothesis is stated on the theorems, not in this predicate.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, Problem (2), pp. 5–6

import Mathlib
import Definitions.Def_VehShare_SeqBounds_IsFeasible2
import Definitions.Def_VehShare_SeqBounds_Rs

namespace VehShare.SeqBounds

/-- **Optimal solutions `q^s` of Problem (2).**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), Problem (2), p. 5, and p. 6 ("where `Δ ≥ K`"): `q^s` maximizes `R_s` over the feasible set.

**Formalization Note.** The standing assumption `Δ ≥ K` is a hypothesis of the theorems that use
it, not part of this predicate. -/
def IsOptimal2 (P : Instance) (Δ : ℝ) (q : P.L → P.L → ℝ) : Prop :=
  IsFeasible2 P Δ q ∧ ∀ q', IsFeasible2 P Δ q' → Rs P q' ≤ Rs P q

end VehShare.SeqBounds


