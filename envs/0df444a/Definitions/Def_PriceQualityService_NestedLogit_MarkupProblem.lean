-- Prove2me | Definitions.Def_PriceQualityService_NestedLogit_MarkupProblem
-- name    : PriceQualityService_NestedLogit_MarkupProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:24.225011+00:00
-- url     : https://prove2.me/theorems/185adc8f-588b-45ca-8733-944f5c65ad95
-- title:
--   Online Supplement pp. 5–6 — the nest-markup problem: $e_x(\rho_x,\mathbf q_x)$, $d_x(\boldsymbol\rho,\mathbf q)$ and $\Pi_M(\boldsymbol\rho,\mathbf q)$ of (EC.6)
-- statement:
--   This file defines the reduced, two-dimensional profit function used in the proof of Theorem 4, in which every product of nest $x$ carries one common markup $\rho_x$.
--
--   In the nested logit model of this mission, write
--   $$
--   u_{xj}(\mathbf q)=\alpha_{xj}q_{xj}-c_{xj}q_{xj}^2-t_x(a_{xj}-b_{xj}q_{xj})+t_xs_{xj}
--   $$
--   for the utility of product $j$ of nest $x$ net of its production and service cost. For a markup vector $\boldsymbol\rho=(\rho_s,\rho_l)$ the nest attractiveness and the nest choice probability are
--   $$
--   e_x(\rho_x,\mathbf q_x)=\sum_{j=1}^{m_x}\exp\bigl(u_{xj}(\mathbf q)-\rho_x\bigr),\qquad
--   d_x(\boldsymbol\rho,\mathbf q)=\frac{e_x(\rho_x,\mathbf q_x)^{1/\mu_1}}{1+e_s(\rho_s,\mathbf q_s)^{1/\mu_1}+e_l(\rho_l,\mathbf q_l)^{1/\mu_1}},
--   $$
--   and the profit as a function of the markups is
--   $$
--   \Pi_M(\boldsymbol\rho,\mathbf q)=\sum_{x\in\{s,l\}}\rho_x\cdot d_x(\boldsymbol\rho,\mathbf q).\qquad\text{(EC.6)}
--   $$
--
--   When the price of every product of nest $x$ is $p_{xj}=\rho_x+c_{xj}q_{xj}^2+t_x(a_{xj}-b_{xj}q_{xj})$, these quantities coincide with $e_x(\mathbf p_x,\mathbf q_x)$, $d_x(\mathbf p,\mathbf q)$ and $\Pi_M(\mathbf p,\mathbf q)$ of the full model; that identity is part of the milestone (EC.6), not of this definition.
--
--   **Formalization Note.** As in the model file, an empty nest has $e_x=0$ and contributes nothing; powers are `Real.rpow` of nonnegative bases.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement pp. 5–6 (PDF pp. 38–39), proof of Theorem 4, (EC.6)

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_Model

namespace PriceQualityService.NestedLogit

/-- Utility of product `i` of nest `x` net of its cost, at markup zero:
`α_xi q_xi − c_xi q_xi² − t_x (a_xi − b_xi q_xi) + t_x s_xi`. With markup `ρ` the product's
attraction is `exp(netUtility − ρ)` (Online Supplement p. 6). -/
def netUtility (M : Model) (q : Vec M) (x : Nest) (i : Fin (M.m x)) : ℝ :=
  M.α x i * q x i - M.c x i * q x i ^ 2 - M.t x * (M.a x i - M.b x i * q x i) + M.t x * M.s x i

/-- Total attractiveness of nest `x` when every product of the nest carries the markup `ρ_x`
(Online Supplement p. 6):
`e_x(ρ_x, q_x) = ∑_{j=1}^{m_x} exp(α_xj q_xj − c_xj q_xj² − t_x (a_xj − b_xj q_xj) + t_x s_xj − ρ_x)`. -/
noncomputable def markupNestAttraction (M : Model) (ρ : Nest → ℝ) (q : Vec M) (x : Nest) : ℝ :=
  ∑ j, Real.exp (netUtility M q x j - ρ x)

/-- First-stage nest probability as a function of the nest markups `ρ = (ρ_s, ρ_l)`
(Online Supplement pp. 5–6): `d_x(ρ, q) = e_x(ρ_x, q_x)^{1/μ₁} / (1 + e_s(ρ_s, q_s)^{1/μ₁} + e_l(ρ_l, q_l)^{1/μ₁})`. -/
noncomputable def markupNestProb (M : Model) (ρ : Nest → ℝ) (q : Vec M) (x : Nest) : ℝ :=
  markupNestAttraction M ρ q x ^ (1 / M.μ₁) /
    (1 + markupNestAttraction M ρ q Nest.s ^ (1 / M.μ₁)
      + markupNestAttraction M ρ q Nest.l ^ (1 / M.μ₁))

/-- Total expected profit as a function of the nest markups (EC.6), Online Supplement p. 6:
`Π_M(ρ, q) = ∑_{x∈{s,l}} ρ_x · d_x(ρ, q)`. -/
noncomputable def markupProfit (M : Model) (ρ : Nest → ℝ) (q : Vec M) : ℝ :=
  ∑ x, ρ x * markupNestProb M ρ q x

end PriceQualityService.NestedLogit


