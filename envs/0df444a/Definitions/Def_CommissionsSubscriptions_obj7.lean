-- Prove2me | Definitions.Def_CommissionsSubscriptions_obj7
-- name    : CommissionsSubscriptions_obj7
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:31:26.883143+00:00
-- url     : https://prove2.me/theorems/d3550d20-ff7d-4911-8bff-ccb5c1de54dc
-- title:
--   Objective $h(q^s,q^b)$ of (6) and (7a)
-- statement:
--   For supplies $q^s$ and demands $q^b$,
--   $$h(q^s,q^b)=\sum_{j\in B}F^{-1}_{b_j}\Bigl(1-\frac{q^b_j}{b_j}\Bigr)q^b_j-\sum_{i\in S}F^{-1}_{s_i}\Bigl(\frac{q^s_i}{s_i}\Bigr)q^s_i-\sum_{i\in S}c_iq^s_i .$$
--   In any equilibrium the platform's revenue is at most $h(q^s,q^b)$ (the marginal agents' surplus is nonnegative), and $h$ is the objective (7a) of the convex relaxation (7).
--
--   **Formalization Note** Valued in the extended reals: a seller term $+\infty$ gives $h=-\infty$, as in the paper. The buyer sum is finite on $[0,b_j]$, so no $\infty-\infty$ arises. The objective does not depend on the flow.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), (6) and (7a), p. 12

import Mathlib
import Definitions.Def_CommissionsSubscriptions_gB
import Definitions.Def_CommissionsSubscriptions_hS

namespace CommissionsSubscriptions

/-- **The function `h(q^s, q^b)` of (6), the objective (7a) of the relaxation (7).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), (6) and (7a), p. 12:
`h(q^s, q^b) = Σ_{j∈B} F⁻¹_{b_j}(1 − q^b_j/b_j) q^b_j − Σ_{i∈S} F⁻¹_{s_i}(q^s_i/s_i) q^s_i
 − Σ_{i∈S} c_i q^s_i`.

**Formalization Note (Reading 1).** Valued in `EReal`. The buyer sum is real (`gB`, finite on
`[0, b_j]`), so no `⊤ − ⊤` arises; a seller term `h_i(s_i) = ⊤` (unbounded support) makes the
value `⊥ = −∞`, as in the paper. The objective does not depend on the flow `x`. -/
noncomputable def obj7 {S B : Type} [Fintype S] [Fintype B] (M : Market S B)
    (qs : S → ℝ) (qb : B → ℝ) : EReal :=
  ((∑ j, gB M j (qb j) : ℝ) : EReal) - ∑ i, hS M i (qs i) - ((∑ i, M.c i * qs i : ℝ) : EReal)

end CommissionsSubscriptions


