-- Prove2me | Definitions.Def_ChannelRebate_Effort_Setting
-- name    : ChannelRebate_Effort_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:17.828046+00:00
-- url     : https://prove2.me/theorems/1f1d9fbe-80fc-4080-b832-22faac375444
-- title:
--   §4.1–4.3, pp. 999–1002 — effort model under ξ ∼ Uniform(0,1), V(e) = ae²/2: Π(Q,e), R(Q,e|T), M, A(e|T), Q̄₀, Q̲₀, Q̲₁, τ, ē, e̲, j, u(T), b(T), T₃, T₁, T₂, L̲, L̄
-- statement:
--   This file fixes the quantity-and-effort model of Taylor (2002), §4, in the uniform specialization of §4.3 that Lemmas 3–6 and Theorem 2 use.
--
--   **Prices and demand.** The retail price is $p$, the production cost $c$, the salvage value $s$ and the wholesale price $w$, with $0<c<w<p$ and $s<c$ (Assumption A1). The retailer chooses an order quantity $Q\ge 0$ and an effort level $e\ge 0$. Demand is $e\xi$, where $\xi\sim\mathrm{Uniform}(0,1)$: its law is Lebesgue measure on $[0,1]$, its distribution function is $\Phi(x)=\int_0^x \mathbf 1_{[0,1]}(y)\,dy$ and $\Gamma(x)=\int_0^x y\,\mathbf 1_{[0,1]}(y)\,dy=\int_0^x \xi\,d\Phi(\xi)$. Effort costs $V(e)=ae^2/2$ with $a>0$.
--
--   **Profits.** With $E\min(Q,e\xi)$, $E(Q-e\xi)^+$ and $E(\min(Q,e\xi)-T)^+$ computed under the law of $e\xi$:
--   $$\Pi(Q,e)=-cQ+pE\min(Q,e\xi)+sE(Q-e\xi)^+-V(e),$$
--   $$R(Q,e\mid T)=-wQ+pE\min(Q,e\xi)+uE(\min(Q,e\xi)-T)^+ +bE(Q-e\xi)^+-V(e),$$
--   $$M(Q,e\mid T)=(w-c)Q-uE(\min(Q,e\xi)-T)^+-(b-s)E(Q-e\xi)^+ .$$
--   $\Pi$ is the integrated channel's profit, $R$ the retailer's profit under the target rebate and returns contract $(w,u,b,T)$: a rebate $u$ per unit sold beyond the target $T$ and a credit $b$ per unsold unit. $M$ is the manufacturer's profit: she sells $Q$ units at $w$, pays the rebate, and buys back unsold units at $b$, salvaging them at $s$. $A(e\mid T)=\sup_{Q\ge0}R(Q,e\mid T)$ is the retailer's best profit at effort $e$, and $\Lambda(\gamma)=\gamma V'(\gamma)-V(\gamma)$ with $V'(\gamma)=a\gamma$.
--
--   **Critical fractiles and thresholds.** $\bar Q_0$, $\underline Q_0$ and $\underline Q_1$ are the positive solutions of $\Phi(\bar Q_0)=\frac{p-c}{p-s}$, $\Phi(\underline Q_0)=\frac{p-w}{p-b}$ and $\Phi(\underline Q_1)=\frac{p+u-w}{p+u-b}$. The threshold $\tau$ is a root, on $[\underline Q_0,\underline Q_1]$, of $f(T)=r(\underline Q_0\mid T)-r(\underline Q_1\mid T)$, where $r(Q\mid T)=-wQ+pE\min(Q,\xi)+bE(Q-\xi)^+ +uE(\min(Q,\xi)-T)^+$ is the no-effort retailer profit with $b$ in place of $s$. The effort levels are $\bar e=(p-s)\Gamma(\bar Q_0)/a$ and $\underline e=(p-b)\Gamma(\underline Q_0)/a$, the solutions of $V'(\bar e)=(p-s)\Gamma(\bar Q_0)$ and $V'(\underline e)=(p-b)\Gamma(\underline Q_0)$. The function $j(T')$ is the maximum of $A(\cdot\mid T')$ on $[0,T'/\tau]$ minus its maximum on $[T'/\tau,\infty)$.
--
--   **The contract terms of Theorem 2.** With $\zeta(T)=4a^2(p-s)^3T^2$,
--   $$u(T)=(w-c)\frac{(p-c)^5}{(p-c)^5-\zeta(T)},\qquad b(T)=s+(w-c)\frac{(p-c)^6-(p-s)\zeta(T)}{(p-c)^6-(p-c)\zeta(T)},\qquad T_3=\frac{(p-c)^3}{2a(p-s)^2}.$$
--   $T_1\in[0,T_3]$ is a fixed point of $m_1(T)=\underline e\tau$ and $T_2\in[0,T_3]$ a fixed point of $m_2(T)=\bar e\tau$, where $\underline e$ and $\tau$ are evaluated at $u=u(T)$, $b=b(T)$. $\underline L(T,w)$ is the retailer's profit under $(w,u(T),b(T),T)$ at effort $\underline e$ and order $\underline e\,\underline Q_0$, and $\bar L(T)$ her profit at effort $\bar e$ and order $\bar e\,\underline Q_1$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** $E\min(Q,e\xi)$ and $E(Q-e\xi)^+$ are the published `expSales` and `expLeftover` of the image law of $\xi$ under $x\mapsto ex$. $\Phi^{-1}$ is never used as a function: each fractile, $\tau$, $j$, $T_1$, $T_2$, $\underline L$ and $\bar L$ is a predicate stating the defining equation (`IsQbar0`, `IsQlow0`, `IsQlow1`, `IsTau`, `IsJ`, `IsFixed1`, `IsFixed2`, `IsLlow`, `IsLbar`). $\bar e$ and $\underline e$ are explicit functions of the fractile they use. $A(e\mid T)$ is a real supremum; it is the true maximum because $R(\cdot,e\mid T)$ is continuous and tends to $-\infty$ (as $b<w$), which the milestone on $A$ asserts. $M$ is not displayed in the paper; it is written from the contract's cash flows. $\bar L$ depends on $w$ through $u(T)$, $b(T)$ and $\underline Q_1$, although the paper writes $\bar L(T)$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), pp. 999–1002, Assumptions A1, A5, §4.1, §4.2, §4.3 (R(Q, e|T), A(e|T), j, ϒ, u(T), b(T), ζ(T), T₃, m₁, m₂, L̲, L̄); τ₀ from §3.2, p. 995

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory CachonCoord.Newsvendor

namespace ChannelRebate.Effort

noncomputable section

/-! Taylor (2002), §4.1–§4.3, pp. 999–1002: the multiplicative sales-effort model under
`ξ ∼ Uniform(0, 1)` and `V(e) = a e² / 2`, the target rebate and returns contract
`(w, u, b, T)`, and the terms `u(T)`, `b(T)`, `T₃`, `T₁`, `T₂`, `L̲`, `L̄` of Theorem 2. -/

/-- The law of `ξ ∼ Uniform(0, 1)` (p. 1001): Lebesgue measure restricted to `[0, 1]`. -/
def unifLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- `Φ(x) = ∫₀ˣ φ(y) dy`, the distribution function of `ξ`, with `φ` the uniform density
`1_{[0,1]}`. -/
def Phi (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y

/-- `Γ(x) = ∫₀ˣ ξ dΦ(ξ)` (§3.1, p. 995), for the uniform density. -/
def Gam (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, y * (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y

/-- The law of demand `e ξ` at effort level `e`: the image of `unifLaw` under `x ↦ e x`. -/
def demandLaw (e : ℝ) : Measure ℝ := unifLaw.map (fun x => e * x)

/-- The cost of effort `V(e) = a e² / 2` (p. 1001). -/
def V (a e : ℝ) : ℝ := a * e ^ 2 / 2

/-- `E(min(Q, D) − T)⁺` for a demand law `D`: the units sold beyond the target `T`. -/
def rebateUnitsLaw (D : Measure ℝ) (Q T : ℝ) : ℝ := ∫ d, max (min Q d - T) 0 ∂D

/-- `E(min(Q, e ξ) − T)⁺`. -/
def rebateUnits (Q e T : ℝ) : ℝ := rebateUnitsLaw (demandLaw e) Q T

/-- The integrated channel's profit (§4.1, p. 999):
`Π(Q, e) = −cQ + pE min(Q, eξ) + sE(Q − eξ)⁺ − V(e)`. -/
def Pi_ (p c s a Q e : ℝ) : ℝ :=
  -c * Q + p * expSales (demandLaw e) Q + s * expLeftover (demandLaw e) Q - V a e

/-- The retailer's profit under a target rebate and returns (§4.3, p. 1000):
`R(Q, e|T) = −wQ + pE min(Q, eξ) + uE(min(Q, eξ) − T)⁺ + bE(Q − eξ)⁺ − V(e)`. -/
def R (p w u b a T Q e : ℝ) : ℝ :=
  -w * Q + p * expSales (demandLaw e) Q + u * rebateUnits Q e T
    + b * expLeftover (demandLaw e) Q - V a e

/-- The manufacturer's profit under a target rebate and returns (not displayed in the paper):
it sells `Q` units at `w`, pays the rebate, and buys back unsold units at `b`, salvaging them
at `s`. -/
def M (c s w u b T Q e : ℝ) : ℝ :=
  (w - c) * Q - u * rebateUnits Q e T - (b - s) * expLeftover (demandLaw e) Q

/-- The no-effort retailer profit `r(Q|T)` of §3.2 (p. 995) with the return credit `b` in
place of `s`; it defines `τ` (§4.3, p. 1000). -/
def rRet (p w u b T Q : ℝ) : ℝ :=
  -w * Q + p * expSales unifLaw Q + b * expLeftover unifLaw Q + u * rebateUnitsLaw unifLaw Q T

/-- `Λ(γ) = γ V′(γ) − V(γ)` (p. 999), with `V′(γ) = a γ`. -/
def Lam (a γ : ℝ) : ℝ := γ * (a * γ) - V a γ

/-- `Q̄₀ = Φ⁻¹((p − c)/(p − s))`, stated by its defining equation. -/
def IsQbar0 (p c s Q : ℝ) : Prop := 0 < Q ∧ Phi Q = (p - c) / (p - s)

/-- `Q̲₀ = Φ⁻¹((p − w)/(p − b))` (§4.2, p. 1000). -/
def IsQlow0 (p w b Q : ℝ) : Prop := 0 < Q ∧ Phi Q = (p - w) / (p - b)

/-- `Q̲₁ = Φ⁻¹((p + u − w)/(p + u − b))` (§4.3, p. 1000). -/
def IsQlow1 (p w u b Q : ℝ) : Prop := 0 < Q ∧ Phi Q = (p + u - w) / (p + u - b)

/-- `τ`: the analogue of `τ₀` with `b` in place of `s` (p. 1000): a root on `[Q̲₀, Q̲₁]` of
`f(T) = r(Q̲₀|T) − r(Q̲₁|T)`. -/
def IsTau (p w u b τ : ℝ) : Prop :=
  ∃ Q0 Q1, IsQlow0 p w b Q0 ∧ IsQlow1 p w u b Q1 ∧ Q0 ≤ τ ∧ τ ≤ Q1 ∧
    rRet p w u b τ Q0 = rRet p w u b τ Q1

/-- `ē`, the solution of `V′(ē) = (p − s)Γ(Q̄₀)` (p. 999), given `Q̄₀ = Qb`. -/
def ebarOf (p s a Qb : ℝ) : ℝ := (p - s) * Gam Qb / a

/-- `e̲`, the solution of `V′(e̲) = (p − b)Γ(Q̲₀)` (p. 1000), given `Q̲₀ = Q0`. -/
def elowOf (p b a Q0 : ℝ) : ℝ := (p - b) * Gam Q0 / a

/-- `(Q, e)` maximizes `f` over `Q ≥ 0, e ≥ 0`. -/
def IsOptimalPair (f : ℝ → ℝ → ℝ) (Q e : ℝ) : Prop :=
  0 ≤ Q ∧ 0 ≤ e ∧ ∀ Q' ≥ 0, ∀ e' ≥ 0, f Q' e' ≤ f Q e

/-- The set of maximizers `(Q, e)` of `f` over `Q ≥ 0, e ≥ 0`. -/
def optimalPairs (f : ℝ → ℝ → ℝ) : Set (ℝ × ℝ) := {x | IsOptimalPair f x.1 x.2}

/-- The set of maximizers of `g` over `[0, ∞)`. -/
def optimalSet (g : ℝ → ℝ) : Set ℝ := {x | 0 ≤ x ∧ ∀ x' ≥ 0, g x' ≤ g x}

/-- `A(e|T) = R(Q*(e), e|T)` (p. 1001): the retailer's best profit at effort `e`, as the supremum
of `R(·, e|T)` over `Q ≥ 0`. -/
def Aeff (p w u b a T e : ℝ) : ℝ := sSup ((fun Q => R p w u b a T Q e) '' Set.Ici 0)

/-- `j(T') = A̲(ẽ|T') − Ā(ê|T')` (p. 1001), as a relation `IsJ … T' j`: `A̲(ẽ|T')` is the
maximum of `A(·|T')` on `[0, T'/τ]` and `Ā(ê|T')` its maximum on `[T'/τ, ∞)`. -/
def IsJ (p w u b a τ T' j : ℝ) : Prop :=
  ∃ x y, IsGreatest ((Aeff p w u b a T') '' Set.Icc 0 (T' / τ)) x ∧
    IsGreatest ((Aeff p w u b a T') '' Set.Ici (T' / τ)) y ∧ j = x - y

/-- `ζ(T) = 4a²(p − s)³T²` (p. 1001). -/
def zeta (p s a T : ℝ) : ℝ := 4 * a ^ 2 * (p - s) ^ 3 * T ^ 2

/-- `u(T) = (w − c)(p − c)⁵/((p − c)⁵ − ζ(T))` (p. 1001). -/
def uT (p c s a w T : ℝ) : ℝ := (w - c) * ((p - c) ^ 5 / ((p - c) ^ 5 - zeta p s a T))

/-- `b(T) = s + (w − c)((p − c)⁶ − (p − s)ζ(T))/((p − c)⁶ − (p − c)ζ(T))` (p. 1001). -/
def bT (p c s a w T : ℝ) : ℝ :=
  s + (w - c) * (((p - c) ^ 6 - (p - s) * zeta p s a T) / ((p - c) ^ 6 - (p - c) * zeta p s a T))

/-- `T₃ = (p − c)³/[2a(p − s)²]` (p. 1001). -/
def T3 (p c s a : ℝ) : ℝ := (p - c) ^ 3 / (2 * a * (p - s) ^ 2)

/-- `T₁ ∈ [0, T₃]` is a fixed point of `m₁(T) = e̲τ`, with `e̲`, `τ` evaluated at
`u = u(T)`, `b = b(T)` (p. 1001). -/
def IsFixed1 (p c s a w T₁ : ℝ) : Prop :=
  0 ≤ T₁ ∧ T₁ ≤ T3 p c s a ∧
    ∃ Q0 τ, IsQlow0 p w (bT p c s a w T₁) Q0 ∧
      IsTau p w (uT p c s a w T₁) (bT p c s a w T₁) τ ∧
      T₁ = elowOf p (bT p c s a w T₁) a Q0 * τ

/-- `T₂ ∈ [0, T₃]` is a fixed point of `m₂(T) = ēτ`, with `τ` evaluated at
`u = u(T)`, `b = b(T)` (p. 1001). -/
def IsFixed2 (p c s a w T₂ : ℝ) : Prop :=
  0 ≤ T₂ ∧ T₂ ≤ T3 p c s a ∧
    ∃ Qb τ, IsQbar0 p c s Qb ∧
      IsTau p w (uT p c s a w T₂) (bT p c s a w T₂) τ ∧
      T₂ = ebarOf p s a Qb * τ

/-- `L̲(T, w) = L` (p. 1002): under `(w, u(T), b(T), T)`, the retailer's profit when she exerts
effort `e̲` and orders `Q₂ = e̲Q̲₀`. -/
def IsLlow (p c s a w T L : ℝ) : Prop :=
  ∃ Q0, IsQlow0 p w (bT p c s a w T) Q0 ∧
    L = R p w (uT p c s a w T) (bT p c s a w T) a T
      (elowOf p (bT p c s a w T) a Q0 * Q0) (elowOf p (bT p c s a w T) a Q0)

/-- `L̄(T) = L` (p. 1002): under `(w, u(T), b(T), T)`, the retailer's profit when she exerts
effort `ē` and orders `Q₃ = ēQ̲₁`. -/
def IsLbar (p c s a w T L : ℝ) : Prop :=
  ∃ Qb Q1, IsQbar0 p c s Qb ∧ IsQlow1 p w (uT p c s a w T) (bT p c s a w T) Q1 ∧
    L = R p w (uT p c s a w T) (bT p c s a w T) a T
      (ebarOf p s a Qb * Q1) (ebarOf p s a Qb)

end

end ChannelRebate.Effort


