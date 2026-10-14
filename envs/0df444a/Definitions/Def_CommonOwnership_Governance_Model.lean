-- Prove2me | Definitions.Def_CommonOwnership_Governance_Model
-- name    : CommonOwnership_Governance_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:11.552485+00:00
-- url     : https://prove2.me/theorems/129b4e00-fee1-4069-aa89-3201c41b7b62
-- title:
--   §3–4, (13), (14), (17), (20), PDF pp. 10–20 — common-ownership weight, optimal monitoring, joint surplus, equilibrium ownership
-- statement:
--   This file sets up the baseline model of Denicolò and Panunzi. Two symmetric firms each have a blockholder who owns a fraction $\beta\in(0,1]$ of the shares; a financial investor buys a stake $s\in[0,\beta]$ from each blockholder, who keeps the residual stake $t=\beta-s$. Each firm's manager diverts a fraction $\xi$ of profits unless monitored, and the investor's influence on managers is $\theta$.
--
--   **Common-ownership weight (17).** Each manager maximizes her own firm's profit plus $\lambda$ times the rival's, where
--   $$\lambda(s)=\frac{\theta s^2}{(\beta-s)^2+\theta s^2}.$$
--
--   **Monitoring (§3.2.1).** A blockholder with residual stake $t$ chooses monitoring $m\in[0,1]$, which cuts the manager's diversion from $\xi$ to $\xi(1-m)$ at private cost $C(m)$ per unit of profit. His payoff per unit of profit is
--   $$t\,[1-\xi(1-m)]-C(m).$$
--   A function $m^*$ is an *optimal monitoring rule* if, for every $t\in[0,\beta]$, $m^*(t)\in[0,1]$ maximizes this objective over $m\in[0,1]$. The quadratic specification (20) is $C(m)=\tfrac12\gamma m^2$.
--
--   **Joint surplus (13)–(15).** The large shareholders' payoff per unit of profit is
--   $$\nu^*(s)=\beta\{1-\xi[1-m^*(\beta-s)]\}-C[m^*(\beta-s)],$$
--   and industry profit is $\Pi^*(s)=P(\lambda(s))$ for an industry-profit function $P$ of the weight $\lambda$. The joint surplus is $S(s)=\nu^*(s)\,\Pi^*(s)$.
--
--   **Equilibrium ownership (Proposition 1, §4.2).** A stake $s$ is an equilibrium level of common ownership if $s\in[0,\beta]$ and $S(s')\le S(s)$ for every $s'\in[0,\beta]$; several equilibria are allowed.
--
--   **Appendix A objects.** Under (20) and $m^*(t)=\xi t/\gamma$ (21), the surplus along an industry-profit path $\Pi^*$ is $S_Q(s)=\nu^*(s)\Pi^*(s)$. The functions of (A3) and (A5) are
--   $$H=-s+\Big[\gamma\beta\frac{1-\xi}{\xi^2}+\tfrac12(\beta^2-s^2)\Big]g,\qquad K=\Big[2\gamma\beta\frac{1-\xi}{\xi^2}+\beta^2\Big]\frac{\Pi^*_+-\Pi^*_0}{\Pi^*_+}-s^{+2},$$
--   where $g$ stands for the semi-elasticity $(\partial\Pi^*/\partial s)(1/\Pi^*)$, and $\Pi^*_0$, $\Pi^*_+$ are industry profits at $s=0$ and $s=s^+$.
--
--   These are the objects of Propositions 2 and 3 and of the steps of their proofs.
--
--   **Formalization Note** `lam θ β s` is $\lambda(s)$; `monitorObj C ξ t m` the blockholder's objective divided by $\pi_i>0$; `IsOptMonitoring C ξ β mstar` the optimality predicate, constraining `mstar` only on $t\in[0,\beta]$; `nuStar`, `jointSurplus` and `IsEqOwnership` are (14), (13) and equilibrium ownership; `surplusQ`, `Hfun`, `Kfun` are the Appendix A objects, with `surplusQ` built from `nuStar` with the cost `quadCost γ` and the rule $t\mapsto\xi t/\gamma$. The product-market game is not modelled: industry profit enters as an arbitrary function `P` of $\lambda$, so statements about it hold for the equilibrium industry profit of any product-market model. Proposition 1 (the bargaining reduction) is not formalized; equilibrium ownership is defined, as in §4.2, as a maximizer of the symmetric surplus (13).
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), pp. 7–17 and 38–39 (PDF pp. 10–20 and 41–42), §3.1–3.2, §4.2, §4.5.1, (13), (14), (15), (17), (20), (21), (A3), (A5)

import Mathlib

namespace CommonOwnership.Governance

/-- (17), p. 13: the weight `λ` a manager puts on the rival firm's profit when the financial
investor holds the stake `s` in both firms, each blockholder keeps `β − s`, and `θ` is the
investor's influence. -/
noncomputable def lam (θ β s : ℝ) : ℝ := θ * s ^ 2 / ((β - s) ^ 2 + θ * s ^ 2)

/-- (20), p. 17: the quadratic monitoring-cost function `C(m) = ½ γ m²`. -/
noncomputable def quadCost (γ m : ℝ) : ℝ := 1 / 2 * γ * m ^ 2

/-- §3.2.1, p. 10: the blockholder's stage-3 objective `t [1 − ξ (1 − m)] − C(m)`, i.e. his payoff
divided by the firm's profit `πᵢ > 0`, where `t = β − s` is his residual stake and `m` his
monitoring. -/
def monitorObj (C : ℝ → ℝ) (ξ t m : ℝ) : ℝ := t * (1 - ξ * (1 - m)) - C m

/-- §3.2.1, p. 10: `mstar t` is the blockholder's optimal monitoring: for every residual stake
`t ∈ [0, β]`, `mstar t ∈ [0, 1]` maximizes `monitorObj C ξ t` over `m ∈ [0, 1]`. -/
def IsOptMonitoring (C : ℝ → ℝ) (ξ β : ℝ) (mstar : ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0:ℝ) β, mstar t ∈ Set.Icc (0:ℝ) 1 ∧
    ∀ m ∈ Set.Icc (0:ℝ) 1, monitorObj C ξ t m ≤ monitorObj C ξ t (mstar t)

/-- (14), p. 13: the large shareholders' aggregate payoff per unit of profit,
`ν*(s) = β {1 − ξ [1 − m*(β − s)]} − C[m*(β − s)]`. -/
def nuStar (C mstar : ℝ → ℝ) (β ξ s : ℝ) : ℝ :=
  β * (1 - ξ * (1 - mstar (β - s))) - C (mstar (β - s))

/-- (13), (15), p. 13: the joint surplus `S(s) = ν*(s) Π*(s)`, with industry profit
`Π*(s) = P(λ(s))` for an industry-profit function `P` of the common-ownership weight. -/
noncomputable def jointSurplus (C mstar P : ℝ → ℝ) (θ β ξ s : ℝ) : ℝ :=
  nuStar C mstar β ξ s * P (lam θ β s)

/-- Proposition 1 and §4.2, pp. 11–13: `s` is an equilibrium level of common ownership iff
`s ∈ [0, β]` maximizes the joint surplus `S` over `[0, β]` (ties allowed). -/
def IsEqOwnership (S : ℝ → ℝ) (β s : ℝ) : Prop :=
  s ∈ Set.Icc (0:ℝ) β ∧ ∀ s' ∈ Set.Icc (0:ℝ) β, S s' ≤ S s

/-- (13)–(14) under (20)–(21), Appendix A, p. 38: the joint surplus `ν*(s) Π*(s)` when the cost is
quadratic and monitoring is `m* = ξ (β − s) / γ`, for an industry-profit path `Pi_ : s ↦ Π*(s)`. -/
noncomputable def surplusQ (β ξ γ : ℝ) (Pi_ : ℝ → ℝ) (s : ℝ) : ℝ :=
  nuStar (quadCost γ) (fun t => ξ * t / γ) β ξ s * Pi_ s

/-- (A3), p. 38: `H = −s + [γβ(1 − ξ)/ξ² + ½(β² − s²)] g`, where `g` stands for the
semi-elasticity `(∂Π*/∂s)(1/Π*)`. -/
noncomputable def Hfun (β ξ γ s g : ℝ) : ℝ :=
  -s + (γ * β * (1 - ξ) / ξ ^ 2 + 1 / 2 * (β ^ 2 - s ^ 2)) * g

/-- (A5), p. 39: `K = [2γβ(1 − ξ)/ξ² + β²] (Π*₊ − Π*₀)/Π*₊ − s⁺²`, with `Pi0 = Π*₀` the industry
profit at `s = 0` and `Pip = Π*₊` the industry profit at `s = s⁺ = sp`. -/
noncomputable def Kfun (β ξ γ sp Pi0 Pip : ℝ) : ℝ :=
  (2 * γ * β * (1 - ξ) / ξ ^ 2 + β ^ 2) * ((Pip - Pi0) / Pip) - sp ^ 2

end CommonOwnership.Governance


