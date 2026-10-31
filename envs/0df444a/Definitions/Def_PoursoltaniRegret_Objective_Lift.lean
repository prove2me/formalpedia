-- Prove2me | Definitions.Def_PoursoltaniRegret_Objective_Lift
-- name    : PoursoltaniRegret_Objective_Lift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:56:31.753985+00:00
-- url     : https://prove2.me/theorems/2ef710b7-18b8-4dd2-b71a-1dc1835451fd
-- title:
--   The literal printed lifted robust problem (16)–(17)
-- statement:
--   For the objective-uncertainty data, a lifted scenario is $u=(\zeta,\rho)\in\mathbb R^{n_\zeta}\times\mathbb R^m$. Define exactly the uncertainty set printed in (17):
--   $$U'=\{(\zeta,\rho):P\zeta\le q,\ B^T\rho=D\zeta+d\}.$$
--   There is no nonnegativity constraint on $\rho$. A recourse action is $a=(\lambda,\gamma)\in\mathbb R^m\times\mathbb R^r$, feasible at $u$ when
--   $$\lambda\ge0,\quad\gamma\ge0,\quad A^T\lambda+W^T\gamma=c,\quad B^T\lambda=D\zeta+d.$$
--   Its profit at first-stage decision $x$ is
--   $$g(x,u,a)=c^Tx+(\psi-Ax)^T\rho-\psi^T\lambda-v^T\gamma.$$
--   These expressions expand the block matrices in (16). The recourse feasible set $Y'(u)$ is independent of $x$ because $A'=0$. A policy $\pi$ is an arbitrary function on the entire lifted real space with $\pi(u)\in Y'(u)$ for every $u\in U'$. Define
--   $$h'(x,u)=\sup_{a\in Y'(u)}g(x,u,a),\quad V_\pi(x)=\inf_{u\in U'}g(x,u,\pi(u)),\quad V(x)=\sup_{\pi\text{ feasible}}V_\pi(x),\quad V^*=\sup_{x\in X}V(x).$$
--   First-stage optimality means $x\in X$ and $V(x)=V^*$. There is no assertion that such an $x$ or an optimizing policy exists.
--
--   The transformed assumptions are evaluated on this constructed problem. Assumption $1'$ is existence of $x\in X,u\in U',a\in Y'(u)$; both $X$ and $U'$ are polyhedra by construction. Assumption $2'$ says $\forall x\in X\,\forall u\in U':Y'(u)\ne\varnothing$. Assumption $3'$ says $\forall x\in X\,\exists u\in U':h'(x,u)<+\infty$. Assumption $4'$ says $\forall x\in X:\inf_{u\in U'}h'(x,u)>-\infty$.
--
--   The policy value and pointwise recourse value are independently defined, and no equality with original regret is built into either definition.
--
--   **Formalization Note** Products of real coordinate spaces encode the concatenated vectors. Paired inequalities are expressed as equalities, and negative-identity blocks as nonnegativity. Extrema use $\mathrm{EReal}$ with the usual empty-set conventions. Policies have no affine or measurable restriction.
-- source:
--   Poursoltani and Delage (2022), Adjustable Robust Optimization Reformulations of Two-Stage Worst-Case Regret Minimization Problems, Operations Research, https://doi.org/10.1287/opre.2021.2159; supplied source.pdf (dated July 10, 2020; printed page = PDF page); §3.1, Eqs. (1)–(3), pp. 4–5; Proposition 2, Eqs. (16)–(17), pp. 9–10

import Definitions.Def_PoursoltaniRegret_Objective_Model

open Matrix

namespace PoursoltaniRegret.Objective

variable {nx ny nz m r s : ℕ} (M : Model nx ny nz m r s)

/-- Equation (17) literally: the multiplier rho has no sign constraint. -/
noncomputable def Model.liftUncertainty : Set ((Fin nz → ℝ) × (Fin m → ℝ)) :=
  {u | u.1 ∈ M.uncertainty ∧ M.Bᵀ *ᵥ u.2 = M.recourseCost u.1}

/-- The six block rows of (16b), reduced to equalities and nonnegativity. -/
noncomputable def Model.liftRecourse (u : (Fin nz → ℝ) × (Fin m → ℝ)) :
    Set ((Fin m → ℝ) × (Fin r → ℝ)) :=
  {a | 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ M.Aᵀ *ᵥ a.1 + M.Wᵀ *ᵥ a.2 = M.c ∧
    M.Bᵀ *ᵥ a.1 = M.recourseCost u.1}

noncomputable def Model.liftProfit (x : Fin nx → ℝ)
    (u : (Fin nz → ℝ) × (Fin m → ℝ)) (a : (Fin m → ℝ) × (Fin r → ℝ)) : ℝ :=
  M.c ⬝ᵥ x + (M.psi - M.A *ᵥ x) ⬝ᵥ u.2 - M.psi ⬝ᵥ a.1 - M.v ⬝ᵥ a.2

noncomputable def Model.liftRecourseValue (x : Fin nx → ℝ)
    (u : (Fin nz → ℝ) × (Fin m → ℝ)) : EReal :=
  ⨆ a : M.liftRecourse u, (M.liftProfit x u a : EReal)

/-- Policies are arbitrary functions on the whole lifted real space. -/
noncomputable def Model.liftPolicies :
    Set (((Fin nz → ℝ) × (Fin m → ℝ)) → ((Fin m → ℝ) × (Fin r → ℝ))) :=
  {pi | ∀ u ∈ M.liftUncertainty, pi u ∈ M.liftRecourse u}

noncomputable def Model.liftPolicyValue (x : Fin nx → ℝ)
    (pi : ((Fin nz → ℝ) × (Fin m → ℝ)) → ((Fin m → ℝ) × (Fin r → ℝ))) : EReal :=
  ⨅ u : M.liftUncertainty, (M.liftProfit x u (pi u) : EReal)

noncomputable def Model.liftBestAt (x : Fin nx → ℝ) : EReal :=
  ⨆ pi : M.liftPolicies, M.liftPolicyValue x pi

noncomputable def Model.liftValue : EReal :=
  ⨆ x : M.firstStage, M.liftBestAt x

noncomputable def Model.liftAssumption1 : Prop :=
  ∃ x ∈ M.firstStage, ∃ u ∈ M.liftUncertainty, ∃ a, a ∈ M.liftRecourse u

noncomputable def Model.liftAssumption2 : Prop :=
  ∀ x ∈ M.firstStage, ∀ u ∈ M.liftUncertainty, (M.liftRecourse u).Nonempty

noncomputable def Model.liftAssumption3 : Prop :=
  ∀ x ∈ M.firstStage, ∃ u ∈ M.liftUncertainty, M.liftRecourseValue x u < ⊤

noncomputable def Model.liftAssumption4 : Prop :=
  ∀ x ∈ M.firstStage, (⊥ : EReal) < ⨅ u : M.liftUncertainty, M.liftRecourseValue x u

noncomputable def Model.isLiftFirstStageOptimal (x : Fin nx → ℝ) : Prop :=
  x ∈ M.firstStage ∧ M.liftBestAt x = M.liftValue

end PoursoltaniRegret.Objective


