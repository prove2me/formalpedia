-- Prove2me | Definitions.Def_PoursoltaniRegret_Objective_Regret
-- name    : PoursoltaniRegret_Objective_Regret
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:56:36.040992+00:00
-- url     : https://prove2.me/theorems/50826d1c-5691-410a-83b6-ea98c4719719
-- title:
--   Recourse profits, nested absolute regret, and Assumptions 1–5
-- statement:
--   For the objective-uncertainty data, write $X,U,Y(x)$ for the feasible sets and $p(x,\zeta,y)=c^Tx+d(\zeta)^Ty$ for profit. The recourse and hindsight profits are
--   $$h(x,\zeta)=\sup_{y\in Y(x)}p(x,\zeta,y),\qquad H(\zeta)=\sup_{\bar x\in X}h(\bar x,\zeta).$$
--   Define the raw worst-case regret and its optimal value by
--   $$R(x)=\sup_{\zeta\in U}\sup_{\bar x\in X}\sup_{\bar y\in Y(\bar x)}\inf_{y\in Y(x)}\big[c^T(\bar x-x)+d(\zeta)^T(\bar y-y)\big],\qquad R^*=\inf_{x\in X}R(x).$$
--   The bracket is real before taking any extrema. This avoids subtraction of infinite profits. A regret-optimal first-stage decision is $x\in X$ with $R(x)=R^*$; existence is not assumed.
--
--   Assumption 1 says that some $x\in X$, $\zeta\in U$ and $y\in Y(x)$ exist. Polyhedrality is already built into the data. Assumption 2 says that $Y(x)$ is nonempty for every $x\in X$ and every $\zeta\in U$. Assumption 3 says $\forall x\in X\,\exists\zeta\in U:\ h(x,\zeta)<+\infty$. Assumption 4 says $\forall x\in X:\inf_{\zeta\in U}h(x,\zeta)>-\infty$. Assumption 5 says $\sup_{\zeta\in U}\sup_{x\in X}h(x,\zeta)<+\infty$, a uniform upper bound.
--
--   These definitions separate the base feasibility hypotheses from optional boundedness hypotheses. Under Assumptions 1–2 and 5 the nested expression is the usual finite-profit regret $\sup_\zeta(H(\zeta)-h(x,\zeta))$.
--
--   **Formalization Note** All extrema are in $\mathrm{EReal}$: empty suprema are $-\infty$, empty infima $+\infty$. Assumption 3 expresses boundedness above; Assumption 2 excludes infeasibility there. The source's interpretation of an unbounded-below WCARM value as zero reported regret is kept separate from this raw optimization value.
-- source:
--   Poursoltani and Delage (2022), Adjustable Robust Optimization Reformulations of Two-Stage Worst-Case Regret Minimization Problems, Operations Research, https://doi.org/10.1287/opre.2021.2159; supplied source.pdf (dated July 10, 2020; printed page = PDF page); Assumptions 1–4, p. 5; Eq. (10), p. 7; §4, Eq. (12), nested convention and Assumption 5, p. 8

import Definitions.Def_PoursoltaniRegret_Objective_Model

open Matrix

namespace PoursoltaniRegret.Objective

variable {nx ny nz m r s : ℕ} (M : Model nx ny nz m r s)

noncomputable def Model.recourseValue (x : Fin nx → ℝ) (z : Fin nz → ℝ) : EReal :=
  ⨆ y : M.recourse x, (M.profit x z y : EReal)

noncomputable def Model.hindsightValue (z : Fin nz → ℝ) : EReal :=
  ⨆ xb : M.firstStage, M.recourseValue xb z

noncomputable def Model.regretAt (x : Fin nx → ℝ) : EReal :=
  ⨆ z : M.uncertainty, ⨆ xb : M.firstStage, ⨆ yb : M.recourse xb,
    ⨅ y : M.recourse x,
      ((M.c ⬝ᵥ (xb.val - x) + M.recourseCost z ⬝ᵥ (yb.val - y.val) : ℝ) : EReal)

noncomputable def Model.regretValue : EReal :=
  ⨅ x : M.firstStage, M.regretAt x

noncomputable def Model.assumption1 : Prop :=
  ∃ x ∈ M.firstStage, ∃ z ∈ M.uncertainty, ∃ y, y ∈ M.recourse x

noncomputable def Model.assumption2 : Prop :=
  ∀ x ∈ M.firstStage, ∀ z ∈ M.uncertainty, (M.recourse x).Nonempty

noncomputable def Model.assumption3 : Prop :=
  ∀ x ∈ M.firstStage, ∃ z ∈ M.uncertainty, M.recourseValue x z < ⊤

noncomputable def Model.assumption4 : Prop :=
  ∀ x ∈ M.firstStage, (⊥ : EReal) < ⨅ z : M.uncertainty, M.recourseValue x z

noncomputable def Model.assumption5 : Prop :=
  (⨆ z : M.uncertainty, ⨆ x : M.firstStage, M.recourseValue x z) < (⊤ : EReal)

noncomputable def Model.isRegretOptimal (x : Fin nx → ℝ) : Prop :=
  x ∈ M.firstStage ∧ M.regretAt x = M.regretValue

end PoursoltaniRegret.Objective


