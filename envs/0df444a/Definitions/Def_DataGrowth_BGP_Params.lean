-- Prove2me | Definitions.Def_DataGrowth_BGP_Params
-- name    : DataGrowth_BGP_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:29.79961+00:00
-- url     : https://prove2.me/theorems/a52ae85c-cd73-4646-9190-f8879f06c842
-- title:
--   §2, pp. 4–7 — parameters, standing ranges, (A.20), $L(t)=L_0e^{nt}$, the constants of (13)–(15), (23), and constant growth
-- statement:
--   The data economy of Cong, Xie and Zhang is described by ten real parameters: the population growth rate $n$, the discount rate $\rho$, the inverse elasticity of intertemporal substitution $\gamma$, the curvature $\sigma$ of the privacy disutility $\phi^\sigma$, the labor elasticity $\beta$ of final-good production, the marginal cost $\psi$ of intermediate goods, the innovation efficiency $\eta$, the data share $\xi$ in innovation, the knowledge spillover $\zeta$, and the initial population $L_0$.
--
--   The **standing ranges** are
--   $$
--   n>0,\ \rho>0,\ \gamma>0,\ \gamma\neq1,\ \sigma>1,\ 0<\beta<1,\ \psi>0,\ \eta>0,\ 0<\xi<1,\ 0<\zeta<1,\ L_0>0 .
--   $$
--   **Proposition A.1's range** (A.20) is: $\zeta>0$; if $\gamma>1$ then $\zeta<1-\frac{\xi}{\sigma}(1-\gamma)$; if $\gamma<1$ then $\zeta<1-(1-\gamma)\left(\frac{n}{\rho}+\frac{\xi}{\sigma}\right)$.
--
--   The population is $L(t)=L_0e^{nt}$. The closed-form constants are
--   $$
--   K_\pi=\frac{\psi^{1-1/\beta}\beta}{(1-\beta)^{1-2/\beta}},\quad K_w=\beta\left[\frac{(1-\beta)^2}{\psi}\right]^{1/\beta-1},\quad K_y=\left[\frac{(1-\beta)^2}{\psi}\right]^{1/\beta-1},\quad A=\left(\frac{\psi}{1-\beta}\right)^{1-1/\beta},
--   $$
--   so that profit (13) is $\pi(t)=K_\pi L_E(t)$, output (14) is $Y(t)=K_yN(t)L_E(t)$, the wage (15) is $w(t)=K_wN(t)$, and $A$ is the planner's markup of (23) and (26). The denominator of the balanced-growth rates is $D=(1-\zeta)\sigma-\xi(1-\gamma)$, and
--   $$
--   g^*=\frac{\sigma n}{D},\qquad g^*_\phi=\frac{(1-\gamma)n}{D}.
--   $$
--   Finally, a function $x$ has **constant growth rate** $g$ if, for every $t>0$, $x(t)>0$ and $\dot x(t)=g\,x(t)$.
--
--   These objects are shared by both economies of the paper.
--
--   **Formalization Note** Powers with real exponents are `Real.rpow`; every base is positive under the standing ranges. Divisions by $D$ are Lean's total division; the theorems that use $g^*$, $g^*_\phi$ make sure $D>0$ follows from their hypotheses.
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, pp. 4–7, §2, (13)–(15); p. 9, (20)–(21); p. 11, (23), (26); p. 13, Figure 1 notes; PDF p. 29, (A.20)

import Mathlib

namespace DataGrowth.BGP

/-- The parameters of the data economy of Cong, Xie, Zhang, *Knowledge Accumulation, Privacy, and
Growth in a Data Economy*, arXiv:2109.10028v1, pp. 4–7, §2 (and Figure 1 notes, p. 13):
`n` population growth rate, `ρ` discount rate, `γ` inverse elasticity of intertemporal
substitution, `σ` curvature of the privacy disutility ϕ^σ, `β` labor elasticity in final-good
production, `ψ` marginal cost of intermediate goods, `η` innovation efficiency, `ξ` data share in
innovation, `ζ` knowledge spillover, `L0` = L(0) the initial population. -/
structure Params where
  n : ℝ
  ρ : ℝ
  γ : ℝ
  σ : ℝ
  β : ℝ
  ψ : ℝ
  η : ℝ
  ξ : ℝ
  ζ : ℝ
  L0 : ℝ

namespace Params

/-- The standing parameter ranges (arXiv:2109.10028v1, p. 7: "η > 0 …, ξ ∈ (0,1) …, 0 < ζ < 1";
p. 13: "σ > 1 ensures the convexity of disutility"; γ ≠ 1 because the flow utility (1) is
(c^{1−γ} − 1)/(1 − γ); 0 < β < 1 and ψ > 0 for (11)–(15); n > 0, ρ > 0, L(0) > 0).

Formalization Note: n > 0 is the paper's standing reading of "grow at a constant rate n" (p. 4). -/
def Standing (P : Params) : Prop :=
  0 < P.n ∧ 0 < P.ρ ∧ 0 < P.γ ∧ P.γ ≠ 1 ∧ 1 < P.σ ∧ 0 < P.β ∧ P.β < 1 ∧ 0 < P.ψ ∧ 0 < P.η ∧
    0 < P.ξ ∧ P.ξ < 1 ∧ 0 < P.ζ ∧ P.ζ < 1 ∧ 0 < P.L0

/-- Proposition A.1's parameter range (A.20) (arXiv:2109.10028v1, PDF p. 29), which the paper adopts
"throughout" (p. 10). -/
def A1Cond (P : Params) : Prop :=
  0 < P.ζ ∧ (1 < P.γ → P.ζ < 1 - P.ξ / P.σ * (1 - P.γ)) ∧
    (P.γ < 1 → P.ζ < 1 - (1 - P.γ) * (P.n / P.ρ + P.ξ / P.σ))

/-- The common denominator (1 − ζ)σ − ξ(1 − γ) of (20)–(21) (p. 9). -/
noncomputable def denom (P : Params) : ℝ := (1 - P.ζ) * P.σ - P.ξ * (1 - P.γ)

/-- The BGP growth rate g* = σn / ((1 − ζ)σ − ξ(1 − γ)) of (20) (p. 9). -/
noncomputable def gStar (P : Params) : ℝ := P.σ * P.n / P.denom

/-- The BGP growth rate of data per capita g*_ϕ = (1 − γ)n / ((1 − ζ)σ − ξ(1 − γ)) of (21) (p. 9). -/
noncomputable def gPhiStar (P : Params) : ℝ := (1 - P.γ) * P.n / P.denom

/-- Population L(t) = L(0) e^{nt} (p. 4: the population grows at the constant rate n). -/
noncomputable def pop (P : Params) (t : ℝ) : ℝ := P.L0 * Real.exp (P.n * t)

/-- The constant of the profit (13) (p. 6): π(t) = ψ^{1−1/β} β / (1 − β)^{1−2/β} · L_E(t). -/
noncomputable def Kpi (P : Params) : ℝ :=
  P.ψ ^ (1 - 1 / P.β) * P.β / (1 - P.β) ^ (1 - 2 / P.β)

/-- The constant of the wage (15) (p. 6): w(t) = β [(1 − β)²/ψ]^{1/β − 1} N(t). -/
noncomputable def Kw (P : Params) : ℝ :=
  P.β * ((1 - P.β) ^ (2 : ℕ) / P.ψ) ^ (1 / P.β - 1)

/-- The constant of output (14) (p. 6): Y(t) = [(1 − β)²/ψ]^{1/β − 1} N(t) L_E(t). -/
noncomputable def Ky (P : Params) : ℝ :=
  ((1 - P.β) ^ (2 : ℕ) / P.ψ) ^ (1 / P.β - 1)

/-- The planner's markup A = (ψ/(1 − β))^{1−1/β} (PDF p. 26; (23) and (26), p. 11). -/
noncomputable def Aconst (P : Params) : ℝ :=
  (P.ψ / (1 - P.β)) ^ (1 - 1 / P.β)

end Params

/-- `x` has the constant growth rate `g` on t > 0: x(t) > 0 and ẋ(t) = g · x(t) for every t > 0
(the balanced-growth-path notion of arXiv:2109.10028v1, p. 9, read per variable). -/
def HasConstGrowth (x : ℝ → ℝ) (g : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → 0 < x t ∧ HasDerivAt x (g * x t) t

end DataGrowth.BGP


