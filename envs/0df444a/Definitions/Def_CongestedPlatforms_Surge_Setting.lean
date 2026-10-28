-- Prove2me | Definitions.Def_CongestedPlatforms_Surge_Setting
-- name    : CongestedPlatforms_Surge_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:41.615574+00:00
-- url     : https://prove2.me/theorems/244f9a6a-d349-40b5-8444-9f887c64c5a8
-- title:
--   §3–§4.1 — congested two-sided platforms: balanced demand and supply (4.2)–(4.7), profit, supply constraint (3.6), symmetric equilibrium on [c/α, 1], utilities (3.1), (3.4), Regions (a), (d)
-- statement:
--   This module sets up the single-homing pricing game of two ride-hailing platforms $i\in\{0,1\}$ with congestion on both sides of the market (§3 and §4.1).
--
--   **Parameters.** The market size (intensity of customers) is $\lambda>0$; $\gamma$ is the customers' sensitivity to congestion; a driver keeps the fraction $\alpha\in(0,1]$ of the price minus a commission $c\ge0$, so the driver's margin on platform $i$ is $x_i=\alpha p_i-c$.
--
--   **Primitive utilities.** A customer at location $v_d\in[0,1]$ on a Hotelling line gets
--   $$u_{d0}=1-v_d-p_0-\gamma\rho_0^2,\qquad u_{d1}=v_d-p_1-\gamma\rho_1^2 \qquad (3.1)$$
--   from platforms 0 and 1, where $\rho_i=d_i/s_i$ is the utilization of platform $i$ (demand over supply). A driver with operating cost $k_{si}$ gets $u_{si}=-k_{si}+(\alpha p_i-c)\rho_i$ (3.4).
--
--   **Balanced demand and supply** (Lemma 1, p. 15). For prices $p_i$ (own) and $p_j$ (rival),
--   $$d^P_i(p_i)=\lambda\frac{(\alpha p_i-c)(1-p_i)}{\alpha p_i-c+\lambda\gamma},\qquad d^F_i(p_i,p_j)=\lambda\frac{(\alpha p_i-c)[\lambda\gamma+(\alpha p_j-c)(1-p_i+p_j)]}{2(\alpha p_i-c)(\alpha p_j-c)+\lambda\gamma[\alpha(p_i+p_j)-2c]},$$
--   $$s^P_i(p_i)=(\alpha p_i-c)\sqrt{\frac{\lambda(1-p_i)}{\alpha p_i-c+\lambda\gamma}},\qquad s^F_i(p_i,p_j)=(\alpha p_i-c)\sqrt{\frac{\lambda[\lambda\gamma+(\alpha p_j-c)(1-p_i+p_j)]}{2(\alpha p_i-c)(\alpha p_j-c)+\lambda\gamma[\alpha(p_i+p_j)-2c]}},$$
--   and the balanced demand $D_i(p_i,p_j)$ and supply $S_i(p_i,p_j)$ equal $d^P_i,s^P_i$ when $d^P_0(p_0)+d^P_1(p_1)\le\lambda$ (Case P, a partially covered market) and $d^F_i,s^F_i$ otherwise (Case F, a fully covered market) — displays (4.2)–(4.7). The formulas are the same for both platforms, so one function serves both.
--
--   **The game** (p. 14). Platform $i$ earns $\Pi_i(p_i,p_j)=[(1-\alpha)p_i+c]\min\{D_i(p_i,p_j),S_i(p_i,p_j)\}$ and must satisfy the supply constraint $D_i(p_i,p_j)\le S_i(p_i,p_j)$ (3.6). A price $p$ is a **symmetric Nash equilibrium** if $p\in[c/\alpha,1]$, $(p,p)$ satisfies (3.6), and every price $q\in[c/\alpha,1]$ that satisfies (3.6) against $p$ earns at most $\Pi(p,p)$.
--
--   **Utilization and utilities at a symmetric profile** (p. 18). When both platforms charge $p$ and the market size is $\lambda$, the utilization is $\rho(p,\lambda)=D(p,p)/S(p,p)$, the customer utilities are $u_{d0}(p,\lambda)=1-v-p-\gamma\rho^2$, $u_{d1}(p,\lambda)=v-p-\gamma\rho^2$ for a customer at location $v$, and the driver utility is $u_s(p,\lambda)=-k+(\alpha p-c)\rho$ for a driver with cost $k$.
--
--   **Regions** (Proposition 1, p. 16), as printed: Region (a) is $\gamma\ge(\tfrac12-c)^2/(2\lambda)$ and $\gamma\ge\lambda(1-c)/(1+2\lambda)$; Region (d) is $\gamma<(\tfrac12-c)^2/(2\lambda)$ and $\gamma\ge\lambda/2$.
--
--   These objects are shared by every statement of the mission: Lemma 1 ties the closed forms to the balance equations, Proposition 1 locates the equilibria, and Proposition 3 compares equilibria at two market sizes.
--
--   **Formalization Note** Since `λ` is a Lean keyword, the market size is the argument `lam`; every object takes the parameters `lam γ α c` explicitly, so that the same game can be compared at two market sizes. The action set $[\underline p,\bar p]$ is read as the natural bounds $[c/\alpha,1]$ (p. 13: supply is nonnegative above $\underline p$; p. 11: demand is nonnegative below $\bar p\le1$). At a symmetric profile the two platforms' best-response conditions are the same inequality, so one condition is stated. Lean's conventions $x/0=0$ and $\sqrt{t}=0$ for $t<0$ apply only outside the model's domain (at $p=c/\alpha$ both demand and supply are $0$ and $\rho$ is $0$).
-- source:
--   Bernstein, DeCroix, Keskin, Competition between Two-Sided Platforms under Demand and Supply Congestion Effects, SSRN 3250224, version of September 16, 2019, pp. 10–18, (3.1a)–(3.6), Lemma 1 (4.2)–(4.7), Proposition 1 regions (a), (d), §4.2 u_di(p, λ), u_si(p, λ)

import Mathlib

namespace CongestedPlatforms.Surge

/-- Case P balanced demand (4.3): `d^P_i(p_i) = λ (αp_i − c)(1 − p_i)/(αp_i − c + λγ)`. -/
noncomputable def dP (lam γ α c p : ℝ) : ℝ :=
  lam * (α * p - c) * (1 - p) / (α * p - c + lam * γ)

/-- Case F balanced demand (4.4) of the platform charging `pi` against a rival charging `pj`. -/
noncomputable def dF (lam γ α c pi pj : ℝ) : ℝ :=
  lam * (α * pi - c) * (lam * γ + (α * pj - c) * (1 - pi + pj)) /
    (2 * (α * pi - c) * (α * pj - c) + lam * γ * (α * (pi + pj) - 2 * c))

/-- Case P balanced supply (4.6): `s^P_i(p_i) = (αp_i − c) √(λ(1 − p_i)/(αp_i − c + λγ))`. -/
noncomputable def sP (lam γ α c p : ℝ) : ℝ :=
  (α * p - c) * Real.sqrt (lam * (1 - p) / (α * p - c + lam * γ))

/-- Case F balanced supply (4.7) of the platform charging `pi` against a rival charging `pj`. -/
noncomputable def sF (lam γ α c pi pj : ℝ) : ℝ :=
  (α * pi - c) * Real.sqrt (lam * (lam * γ + (α * pj - c) * (1 - pi + pj)) /
    (2 * (α * pi - c) * (α * pj - c) + lam * γ * (α * (pi + pj) - 2 * c)))

/-- Balanced demand (4.2) of the platform charging `pi` against a rival charging `pj`:
Case P when `d^P(p_i) + d^P(p_j) ≤ λ`, Case F otherwise. -/
noncomputable def D (lam γ α c pi pj : ℝ) : ℝ :=
  if dP lam γ α c pi + dP lam γ α c pj ≤ lam then dP lam γ α c pi else dF lam γ α c pi pj

/-- Balanced supply (4.5), with the same case switch as (4.2). -/
noncomputable def S (lam γ α c pi pj : ℝ) : ℝ :=
  if dP lam γ α c pi + dP lam γ α c pj ≤ lam then sP lam γ α c pi else sF lam γ α c pi pj

/-- Platform profit `Π_i(p_i, p_j) = [(1 − α)p_i + c] min{D_i, S_i}` (p. 14). -/
noncomputable def profit (lam γ α c pi pj : ℝ) : ℝ :=
  ((1 - α) * pi + c) * min (D lam γ α c pi pj) (S lam γ α c pi pj)

/-- The supply constraint (3.6): `D_i(p_i, p_j) ≤ S_i(p_i, p_j)`. -/
def SupplyOK (lam γ α c pi pj : ℝ) : Prop :=
  D lam γ α c pi pj ≤ S lam γ α c pi pj

/-- `(p, p)` is a symmetric Nash equilibrium of the pricing game (p. 14) on the action set
`[p̲, p̄] = [c/α, 1]`: `p` satisfies (3.6), and no price `q ∈ [c/α, 1]` satisfying (3.6) against
`p` earns a higher profit. -/
def IsSymNE (lam γ α c p : ℝ) : Prop :=
  c / α ≤ p ∧ p ≤ 1 ∧ SupplyOK lam γ α c p p ∧
    ∀ q : ℝ, c / α ≤ q → q ≤ 1 → SupplyOK lam γ α c q p →
      profit lam γ α c q p ≤ profit lam γ α c p p

/-- Utilization `ρ = D/S` when both platforms charge `p` and the market size is `lam`. -/
noncomputable def rho (lam γ α c p : ℝ) : ℝ :=
  D lam γ α c p p / S lam γ α c p p

/-- Utility (3.1a) of a customer at location `v` using platform 0, both platforms charging `p`,
market size `lam`. -/
noncomputable def uD0 (lam γ α c v p : ℝ) : ℝ :=
  1 - v - p - γ * (rho lam γ α c p) ^ 2

/-- Utility (3.1b) of a customer at location `v` using platform 1, both platforms charging `p`,
market size `lam`. -/
noncomputable def uD1 (lam γ α c v p : ℝ) : ℝ :=
  v - p - γ * (rho lam γ α c p) ^ 2

/-- Utility (3.4) of a driver with operating cost `k`, both platforms charging `p`,
market size `lam`. -/
noncomputable def uS (lam γ α c k p : ℝ) : ℝ :=
  -k + (α * p - c) * rho lam γ α c p

/-- Region (a) of Proposition 1 (p. 16), as printed. -/
def RegionA (lam γ c : ℝ) : Prop :=
  (1 / 2 - c) ^ 2 / (2 * lam) ≤ γ ∧ lam * (1 - c) / (1 + 2 * lam) ≤ γ

/-- Region (d) of Proposition 1 (p. 16), as printed. -/
def RegionD (lam γ c : ℝ) : Prop :=
  γ < (1 / 2 - c) ^ 2 / (2 * lam) ∧ lam / 2 ≤ γ

end CongestedPlatforms.Surge


