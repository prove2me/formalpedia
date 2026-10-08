-- Prove2me | Definitions.Def_ChannelRebate_ReturnsEffort_Setting
-- name    : ChannelRebate_ReturnsEffort_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:51.455982+00:00
-- url     : https://prove2.me/theorems/e7e43aad-6709-4c9b-ad71-0021a77b16a3
-- title:
--   §3.1, §4.1–4.2, pp. 994–1000 — demand density (A4), Φ, Γ, effort cost (A5), Λ, and the retailer's profit under returns with effort
-- statement:
--   This file fixes the objects of Taylor's quantity-and-effort model with returns (Management Science 2002, §4).
--
--   **Demand (Assumption A4).** The demand factor $\xi$ is a random variable with a density $\varphi$ on $[0,\infty)$: $\varphi$ is measurable, $\varphi(\xi)=0$ for $\xi<0$, $\varphi(\xi)>0$ for every $\xi\ge 0$, $\int\varphi=1$, and $\xi$ has a finite mean. Its law is the measure with density $\varphi$, and
--   $$\Phi(Q)=\int_0^Q\varphi(\xi)\,d\xi,\qquad \Gamma(Q)=\int_0^Q \xi\,d\Phi(\xi)=\int_0^Q \xi\,\varphi(\xi)\,d\xi .$$
--
--   **Effort cost (Assumption A5).** Exerting effort $e\ge 0$ costs $V(e)$, where $V$ is strictly convex and strictly increasing on $[0,\infty)$ and $V(0)=0$. For a derivative $V'$ of $V$,
--   $$\Lambda(\gamma)=\gamma\,V'(\gamma)-V(\gamma).$$
--
--   **Retailer profit under returns.** Demand is $e\xi$. The retailer buys at the wholesale price $w$, sells at the retail price $p$, and the manufacturer pays a return credit $b$ for each unsold unit. Her expected profit from ordering $Q$ and exerting effort $e$ is
--   $$\underline{R}_b(Q,e)=-wQ+p\,E\min(Q,e\xi)+b\,E(Q-e\xi)^+-V(e).$$
--   It is the integrated channel's profit $\Pi(Q,e)=-cQ+pE\min(Q,e\xi)+sE(Q-e\xi)^+-V(e)$ of §4.1 with $w$ in place of $c$ and $b$ in place of $s$, and also the target-rebate-and-returns profit $R(Q,e\mid T)$ of §4.3 with rebate $u=0$.
--
--   **Optimality.** An order $Q$ is optimal for a profit $r$ when $Q\ge 0$ and $r(Q')\le r(Q)$ for all $Q'\ge 0$. A pair $(Q,e)$ is optimal for $f$ when $Q\ge0$, $e\ge0$ and $f(Q',e')\le f(Q,e)$ for all $Q'\ge0$, $e'\ge0$.
--
--   These are the objects of Proposition 4 and of the §4.2 characterization of the retailer's optimal order and effort.
--
--   **Formalization Note** The expectations $E\min(Q,e\xi)$ and $E(Q-e\xi)^+$ are the published `expSales` and `expLeftover` applied to the image of the law of $\xi$ under $x\mapsto ex$. The strictness of convexity and monotonicity of $V$ follows the paper's convention on p. 995 ("All functions described as concave, convex, increasing, or decreasing are strictly so"). $\Lambda$ takes the derivative $V'$ as an argument; the theorems pin it by a `HasDerivAt` hypothesis on $(0,\infty)$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 994, §3.1 and Assumptions A1, A4; p. 995, definition of Γ and the strictness convention; p. 999, §4.1, Assumption A5, Π(Q, e) and Λ; p. 1000, §4.2; §4.3 R(Q, e|T) with u = 0

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

namespace ChannelRebate.ReturnsEffort

open MeasureTheory

/-- Taylor (2002), §3.1 and Assumption A4, p. 994: demand `ξ` has a density `φ` on `[0, ∞)`
with `φ(ξ) > 0` for every `ξ ≥ 0`, and a finite mean. -/
structure Demand where
  φ : ℝ → ℝ
  measurable_φ : Measurable φ
  φ_eq_zero_of_neg : ∀ ξ, ξ < 0 → φ ξ = 0
  φ_pos : ∀ ξ, 0 ≤ ξ → 0 < φ ξ
  integrable_φ : Integrable φ
  integral_φ : ∫ ξ, φ ξ = 1
  integrable_mul_φ : Integrable (fun ξ => ξ * φ ξ)

/-- The law of `ξ`: Lebesgue measure with density `φ`. -/
noncomputable def Demand.law (D : Demand) : Measure ℝ :=
  volume.withDensity (fun ξ => ENNReal.ofReal (D.φ ξ))

/-- The distribution function `Φ(Q) = ∫₀^Q φ(ξ) dξ` (p. 994). -/
noncomputable def Phi (D : Demand) (Q : ℝ) : ℝ := ∫ ξ in (0)..Q, D.φ ξ

/-- `Γ(Q) = ∫₀^Q ξ dΦ(ξ)` (p. 995). -/
noncomputable def Gam (D : Demand) (Q : ℝ) : ℝ := ∫ ξ in (0)..Q, ξ * D.φ ξ

/-- Assumption A5, p. 999, with the strictness convention of p. 995: the effort cost `V` is
strictly convex and strictly increasing on `[0, ∞)`, and `V(0) = 0`. -/
structure EffortCost where
  V : ℝ → ℝ
  V_zero : V 0 = 0
  strictMonoOn : StrictMonoOn V (Set.Ici 0)
  strictConvexOn : StrictConvexOn ℝ (Set.Ici 0) V

/-- The retailer's expected profit under returns alone with return credit `b`, order `Q` and
effort `e` (§4.1–4.2, pp. 999–1000; `R(Q, e | T)` of §4.3 with `u = 0`):
`R̲_b(Q, e) = −wQ + pE min(Q, eξ) + bE(Q − eξ)⁺ − V(e)`. The demand `eξ` has the image law of
`ξ` under `x ↦ e x`. -/
noncomputable def returnsProfit (p w b : ℝ) (D : Demand) (V : EffortCost) (Q e : ℝ) : ℝ :=
  -w * Q + p * CachonCoord.Newsvendor.expSales (D.law.map (fun x => e * x)) Q
    + b * CachonCoord.Newsvendor.expLeftover (D.law.map (fun x => e * x)) Q - V.V e

/-- `Λ(γ) = γ V′(γ) − V(γ)` (p. 999), for a given derivative `V'` of `V`. -/
def Lam (V : EffortCost) (V' : ℝ → ℝ) (γ : ℝ) : ℝ := γ * V' γ - V.V γ

/-- The set of optimal orders of a profit `r : ℝ → ℝ`: its maximizers over `Q ≥ 0`. -/
def optimalOrders (r : ℝ → ℝ) : Set ℝ := {Q | 0 ≤ Q ∧ ∀ Q', 0 ≤ Q' → r Q' ≤ r Q}

/-- `(Q, e)` is an optimal order–effort pair of `f`: it maximizes `f` over `Q ≥ 0, e ≥ 0`. -/
def IsOptimalPair (f : ℝ → ℝ → ℝ) (Q e : ℝ) : Prop :=
  0 ≤ Q ∧ 0 ≤ e ∧ ∀ Q' e', 0 ≤ Q' → 0 ≤ e' → f Q' e' ≤ f Q e

end ChannelRebate.ReturnsEffort


