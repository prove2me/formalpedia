-- Prove2me | Definitions.Def_NetworkDuopoly_Asymmetry_bestResponse
-- name    : NetworkDuopoly_Asymmetry_bestResponse
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:04.876219+00:00
-- url     : https://prove2.me/theorems/a866d285-48e3-4df5-96be-d9649478b253
-- title:
--   Global share best responses and pure Nash equilibrium
-- statement:
--   For common quality $\alpha\in\mathbb R$, strength $\gamma\ge0$, and rival share $y\in[0,1]$, let $R_{\alpha,\gamma}$ denote the normalized extended-real revenue. The best-response correspondence and equilibrium predicate are
--   $$
--   \operatorname{BR}_{\alpha,\gamma}(y)=\{x\in[0,1]:\ \forall u\in[0,1],\ R_{\alpha,\gamma}(u,y)\le R_{\alpha,\gamma}(x,y)\},
--   $$
--   $$
--   \operatorname{NE}_{\alpha,\gamma}(x,y)\ \Longleftrightarrow\ x\in\operatorname{BR}_{\alpha,\gamma}(y)\ \text{and}\ y\in\operatorname{BR}_{\alpha,\gamma}(x).
--   $$
--   Each best response is a global maximizer. Ties are retained, and every allowed unilateral deviation, including zero, is compared. The two players choose independent shares, each uniform across customers as required by Assumption 2.
--
--   **Formalization Note** Membership in both best-response sets imposes $x,y\in[0,1]$; interiority is not built into equilibrium. Infeasible positive deviations with $u+y\ge1$ receive $-\infty$, and zero always yields zero. Thus using a fixed interval of deviations implements the opponent-dependent constraint of equation (7). All functions are total on real parameters, but only the stated game domain has economic meaning. There is no default selection from an empty or tied argmax.
-- source:
--   Chen and Chen (2021), Duopoly Competition with Network Effects in Discrete Choice Models, https://doi.org/10.1287/opre.2020.2079; supplied artifact pp. 13–17 (PDF 13–17), §3.2, Assumptions 1–3 and equation (7); p. ec1 (PDF 45), boundary payoffs.

import Definitions.Def_NetworkDuopoly_Asymmetry_revenue

namespace NetworkDuopoly.Asymmetry

/- Imported declaration bodies (verbatim), included for standalone audit.
noncomputable def revenue (α γ x y : ℝ) : EReal :=
  if x = 0 then 0
  else if 0 < x ∧ x + y < 1 then
    ((x * (α + γ * x / 2 - Real.log x + Real.log (1 - x - y)) : ℝ) : EReal)
  else ⊥
-/

def bestResponse (α γ y : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ u ∈ Set.Icc (0 : ℝ) 1, revenue α γ u y ≤ revenue α γ x y}

def IsEquilibrium (α γ x y : ℝ) : Prop :=
  x ∈ bestResponse α γ y ∧ y ∈ bestResponse α γ x

end NetworkDuopoly.Asymmetry


