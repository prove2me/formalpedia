-- Prove2me | Definitions.Def_DataGrowth_BGP_Planner
-- name    : DataGrowth_BGP_Planner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:07.856798+00:00
-- url     : https://prove2.me/theorems/721f2961-2366-499f-8191-fb06b3dc8bc4
-- title:
--   §3.2, p. 11 and Online Appendix 1.4 — the planner's necessary-condition system (25)–(27), (A.7)–(A.10) and its BGP
-- statement:
--   A path of the **social planner's economy** consists of per-capita consumption $c$, data per capita $\phi$, varieties $N$, labor shares $l_R,l_E$, and the shadow prices $\lambda$ (of the resource constraint) and $\mu$ (of the innovation frontier).
--
--   It satisfies the planner's **necessary-condition system** if, for every $t>0$, all seven are positive and
--   $$
--   \begin{aligned}
--   &(25)\ \ \dot N=\eta N^\zeta\phi^\xi l_R^{1-\xi}L, \qquad (26)\ \ c=A\beta N l_E, \qquad (27)\ \ l_R+l_E=1,\\
--   &(\text{A.7})\ \ c^{-\gamma}-\lambda=0,\\
--   &(\text{A.8})\ \ -\sigma\phi^{\sigma-1}+\mu\xi\eta N^\zeta\phi^{\xi-1}l_R^{1-\xi}L=0,\\
--   &(\text{A.9})\ \ \lambda\beta A N-\mu\eta(1-\xi)N^\zeta\phi^\xi l_R^{-\xi}L=0,\\
--   &(\text{A.10})\ \ \lambda A\beta l_E+\mu\eta\zeta N^{\zeta-1}\phi^\xi l_R^{1-\xi}L=-\dot\mu+(\rho-n)\mu .
--   \end{aligned}
--   $$
--   A **balanced growth path** of the planner is a solution along which each of $c,\phi,N,l_R,l_E,\lambda,\mu$ grows at a constant rate of its own.
--
--   These are the first-order conditions of the current-value Hamiltonian of the planner's problem (24)–(27), the system the paper solves to obtain Proposition 3.
--
--   **Formalization Note** The optimal control problem (24) itself is not formalized (Mathlib has no Pontryagin maximum principle); the paper states that its solution "can be expressed by the seven equations from (25) to (27) and from (A.7) to (A.10)" (PDF p. 27), and the planner's balanced growth path here is a balanced growth path of that system. Time runs over $t>0$.
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, p. 11, §3.2, (24)–(27); PDF pp. 26–27, Online Appendix 1.4, (A.7)–(A.10)

import Mathlib
import Definitions.Def_DataGrowth_BGP_Params

namespace DataGrowth.BGP

/-- A time path of the social planner's economy (arXiv:2109.10028v1, §3.2, p. 11, and Online
Appendix 1.4, PDF pp. 26–27): per-capita consumption `c`, data per capita `phi` (ϕ), varieties `N`,
labor shares `lR`, `lE`, and the shadow prices `lam` (λ, of the resource constraint (26)) and `mu`
(μ, of the innovation frontier (25)). -/
structure PlanPath where
  c : ℝ → ℝ
  phi : ℝ → ℝ
  N : ℝ → ℝ
  lR : ℝ → ℝ
  lE : ℝ → ℝ
  lam : ℝ → ℝ
  mu : ℝ → ℝ

/-- The social planner's necessary-condition system (Cong, Xie, Zhang, *Knowledge Accumulation,
Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, p. 11, (25)–(27), and Online Appendix
1.4, PDF pp. 26–27, (A.7)–(A.10)), required at every time t > 0:
* positivity of c, ϕ, N, l_R, l_E, λ, μ, and (27) l_R + l_E = 1;
* (25) Ṅ = η N^ζ ϕ^ξ l_R^{1−ξ} L;
* (26) c = A β N l_E with A = (ψ/(1 − β))^{1−1/β};
* (A.7) c^{−γ} − λ = 0;
* (A.8) −σ ϕ^{σ−1} + μ ξ η N^ζ ϕ^{ξ−1} l_R^{1−ξ} L = 0;
* (A.9) λ β A N − μ η (1 − ξ) N^ζ ϕ^ξ l_R^{−ξ} L = 0;
* (A.10) λ A β l_E + μ η ζ N^{ζ−1} ϕ^ξ l_R^{1−ξ} L = −μ̇ + (ρ − n) μ.

Formalization Note: these are the necessary conditions of the current-value Hamiltonian of the
planner's problem (24)–(27), exactly the system the paper solves ("This system can be expressed by
the seven equations from (25) to (27) and from (A.7) to (A.10)", PDF p. 27). The optimal control
problem (24) itself is not formalized (Mathlib has no Pontryagin maximum principle); "the planner's
balanced growth path" means a balanced growth path of this system. Time runs over t > 0. Real powers
are `Real.rpow` on positive bases. -/
def IsPlanEq (P : Params) (S : PlanPath) : Prop :=
  ∀ t : ℝ, 0 < t →
    (0 < S.c t ∧ 0 < S.phi t ∧ 0 < S.N t ∧ 0 < S.lR t ∧ 0 < S.lE t ∧ 0 < S.lam t ∧
      0 < S.mu t) ∧
    -- (27)
    S.lE t + S.lR t = 1 ∧
    -- (25)
    HasDerivAt S.N
      (P.η * S.N t ^ P.ζ * S.phi t ^ P.ξ * S.lR t ^ (1 - P.ξ) * P.pop t) t ∧
    -- (26)
    S.c t = P.Aconst * P.β * S.N t * S.lE t ∧
    -- (A.7)
    S.c t ^ (-P.γ) - S.lam t = 0 ∧
    -- (A.8)
    -P.σ * S.phi t ^ (P.σ - 1) +
        S.mu t * P.ξ * P.η * S.N t ^ P.ζ * S.phi t ^ (P.ξ - 1) * S.lR t ^ (1 - P.ξ) * P.pop t
      = 0 ∧
    -- (A.9)
    S.lam t * P.β * P.Aconst * S.N t -
        S.mu t * P.η * (1 - P.ξ) * S.N t ^ P.ζ * S.phi t ^ P.ξ * S.lR t ^ (-P.ξ) * P.pop t
      = 0 ∧
    -- (A.10)
    (∃ dmu : ℝ, HasDerivAt S.mu dmu t ∧
      S.lam t * P.Aconst * P.β * S.lE t +
          S.mu t * P.η * P.ζ * S.N t ^ (P.ζ - 1) * S.phi t ^ P.ξ * S.lR t ^ (1 - P.ξ) * P.pop t
        = -dmu + (P.ρ - P.n) * S.mu t)

/-- The constant growth rates of a planner's balanced growth path: of c (`gc`), ϕ (`gphi`),
N (`gN`), l_R (`glR`), l_E (`glE`), λ (`glam`) and μ (`gmu`). -/
structure PlanRates where
  gc : ℝ
  gphi : ℝ
  gN : ℝ
  glR : ℝ
  glE : ℝ
  glam : ℝ
  gmu : ℝ

/-- A balanced growth path of the planner's necessary-condition system (arXiv:2109.10028v1, p. 9
and Online Appendix 1.4, PDF pp. 26–28): a path satisfying `IsPlanEq` along which each of
c, ϕ, N, l_R, l_E, λ, μ grows at its own constant rate.

Formalization Note: as for the decentralized economy, "all variables growing at the same constant
rate" (p. 9) is read as each variable growing at a constant rate of its own. The planner's BGP is a
BGP of the Hamiltonian necessary conditions, not of the optimization problem (24), which is not
formalized. -/
def IsPlanBGP (P : Params) (S : PlanPath) (Q : PlanRates) : Prop :=
  IsPlanEq P S ∧
    HasConstGrowth S.c Q.gc ∧ HasConstGrowth S.phi Q.gphi ∧ HasConstGrowth S.N Q.gN ∧
    HasConstGrowth S.lR Q.glR ∧ HasConstGrowth S.lE Q.glE ∧ HasConstGrowth S.lam Q.glam ∧
    HasConstGrowth S.mu Q.gmu

end DataGrowth.BGP


