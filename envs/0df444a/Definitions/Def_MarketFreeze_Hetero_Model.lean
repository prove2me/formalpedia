-- Prove2me | Definitions.Def_MarketFreeze_Hetero_Model
-- name    : MarketFreeze_Hetero_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:02.67404+00:00
-- url     : https://prove2.me/theorems/6dd1cb2f-147d-49a6-8365-58503f3b3265
-- title:
--   §2–§3.2, pp. 7–21 — parameters, Assumptions 1–5, E^hom (8), π^hom_s (9), π^hom_ns (10), ∆π^hom (11), α (6), price (13), E^het (14), IC (A2), profits, equilibrium
-- statement:
--   Song and Thakor's model of bank screening, capital structure and interbank loan trading, with the macro-uncertainty fully integrated out (§3 sets the reuse cost of screening information to $\kappa=0$). All objects are explicit real functions of the boom probability $\theta$ and the market tightness $n$.
--
--   **Parameters.** A good loan pays $X$, every loan needs funding $I$, screening costs $c$, the new asset's pledgeable fraction is $\delta$, a unit of equity costs insiders $\psi$, the interbank market efficiency is $\lambda$, the boom probability ranges over $[0,\bar\theta]$, and $Y(\theta)$ is the bank's charter value. The standing restrictions are $I>0$, $\delta\in(0,1)$, $0\le\bar\theta<I/X$, $c>0$, $\psi>0$.
--
--   **Assumptions 1–5.**
--   1. $(2-\delta)I<X<\min\{2I,\,2[(1+\bar\theta)^{-1}+(1-\delta)]I\}$.
--   2. $Y$ is increasing, concave and differentiable on $[0,\bar\theta]$, with $Y'(\bar\theta)>2(X-I+c)/(1-\bar\theta)^2$ and $Y(0)<2c$.
--   3. $X-I-c-\psi[2c-Y(0)]>0$.
--   4. $\psi\,[Y'(0)-2(X-I+c)/(1-\bar\theta)^2]+0.5\,Y'(0)\le X+0.5\,[Y(0)+I]$.
--   5. $\lambda\in[0,1]$ and the seller's meeting probability is $\alpha(n)=\lambda n/(1+n)$.
--
--   **Benchmark quantities.**
--   $$E^{hom}(\theta)=\frac{2\theta(X-I)+2c}{1-\theta}-Y(\theta),\qquad \pi^{hom}_s(\theta)=X-I-\psi E^{hom}(\theta)-c,$$
--   $$\pi^{hom}_{ns}(\theta)=[\theta+0.5(1-\theta)]X-I+\theta(X-I)-0.5(1-\theta)Y(\theta),\qquad \Delta\pi^{hom}=\pi^{hom}_s-\pi^{hom}_{ns}.$$
--
--   **Trading quantities.** The buyer meets a seller with probability $\lambda/(1+n)$ (the paper's $\alpha(n)/n$), has bargaining power $\beta=1/(1+n)$, the Nash product is $(X-p)^\beta(p-I)^{1-\beta}$, the price is $p(n)=X-(X-I)/(1+n)$ and the buyer's equity is $E^{het}(\theta,n)=E^{hom}(\theta)-\lambda(X-p)/(1+n)$. The buyer's incentive constraint (A2) compares
--   $$-E-\psi E+0.5(X-D+X-I)+0.5E+0.5(1-\theta)\tfrac{\alpha(n)}{n}(X-p)-c$$
--   with $\max\{-\psi E,\ -E-\psi E+[\theta+0.5(1-\theta)](X-D+X-I)-0.5(1-\theta)Y(\theta)\}$. A buyer earns the left side at $E=E^{het}$, $D=I-E^{het}$; a seller earns $\pi^{hom}_{ns}(\theta)+0.5(1-\theta)\alpha(n)(p-I)$; a sole seller among buyers earns $\pi^{hom}_{ns}(\theta)+0.5\lambda(1-\theta)(X-I)$. The left side of (15) is $\lambda(X-I)\big[\tfrac{1-\theta}{2}\tfrac{n-1}{n+1}-\tfrac{\psi}{(n+1)^2}\big]$.
--
--   **Conditions of the proof of Proposition 2.** (A1) is $0.5(1-\bar\theta)X/(1+2\psi(1-\bar\theta)^{-1})-\bar\theta(X-I)+0.5(1-\bar\theta)Y(\bar\theta)<c<0.5X/(1+2\psi)+0.5Y(0)$; (A3) is $\Delta\pi^{hom}(0)>0.5\lambda(X-I)$; (A6) is $\Delta\pi^{hom}(\bar\theta)<-0.5\lambda(1-\bar\theta)(X-I)-\psi\lambda(X-I)$; (A4) at $\theta$ is $-\Delta\pi^{hom}(\theta)+0.5\lambda(1-\theta)(X-I)=0$; (A7) at $\theta$ is $\Delta\pi^{hom}(\theta)+0.5\lambda(1-\theta)(X-I)+\psi\lambda(X-I)=0$.
--
--   **Equilibrium.** With the market closed, the reduced outcome is a Boolean screening choice and an equity amount: screening holds exactly $E^{hom}$ and requires $\pi^{hom}_s>\pi^{hom}_{ns}$; otherwise the bank does not screen and holds zero equity. Equality is assigned to no screening as in footnote 21. With the market open, an equilibrium at $\theta$ is a buyer share $s\in[0,1]$ (buyers hold $E^{het}$ and screen, sellers hold no equity and do not screen; tightness $n=s/(1-s)$) such that: if $s=1$, a sole seller does not earn more than a screening bank $\pi^{hom}_s(\theta)$; if $s=0$, a sole buyer (at $n=0$) does not earn more than $\pi^{hom}_{ns}(\theta)$; if $0<s<1$, buyers and sellers earn the same.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The paper prints (A6) with $+\psi\lambda(X-I)$; the sentence before it requires the sole buyer's gain $\Delta\pi^{hom}(\bar\theta)+0.5\lambda(1-\bar\theta)(X-I)+\psi\lambda(X-I)$ to be negative, which is the sign used here (with the printed sign Proposition 2 fails on an explicit instance). $c>0$, $\psi>0$ and differentiability of $Y$ (the paper's "smooth function of $\theta$") are readings of the text; $Y'$ is the two-sided derivative of $Y:\mathbb R\to\mathbb R$. The buyer's meeting probability takes its limit value $\lambda$ at $n=0$. The corner conditions of the equilibrium are weak inequalities; the all-buyer corner uses the sole seller's limiting profit as $n\to\infty$.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), §2–§3.2, pp. 7–21 (Assumptions 1–5, pp. 10–12; (6)–(14)); Appendix A, (A1)–(A9), pp. 34–37

import Mathlib

namespace MarketFreeze.Hetero

/-- Exogenous parameters of Song–Thakor's model (§2): `X` the date-2 payoff of a good loan,
`I` the financing need of a loan, `c` the date-0 screening cost, `δ` the pledgeable fraction of
the new asset, `ψ` the unit cost of equity to insiders, `lam` the interbank market efficiency `λ`,
`θbar` the upper bound `θ̄` of the boom probability, `Y` the charter value `Y(θ)`. -/
structure Params where
  X : ℝ
  I : ℝ
  c : ℝ
  δ : ℝ
  ψ : ℝ
  lam : ℝ
  θbar : ℝ
  Y : ℝ → ℝ

/-- Standing restrictions of §2: `I > 0`, `δ ∈ (0,1)`, `θ ∈ [0, θ̄]` with `θ̄ < I/X`; and the
readings `c > 0` (screening is a cost) and `ψ > 0` (equity is costly). -/
def Standing (P : Params) : Prop :=
  0 < P.I ∧ 0 < P.δ ∧ P.δ < 1 ∧ 0 ≤ P.θbar ∧ P.θbar < P.I / P.X ∧
  0 < P.c ∧ 0 < P.ψ

/-- Assumption 1 (Bank Debt Capacity), display (1):
`(2 − δ)I < X < min{2I, 2[(1 + θ̄)⁻¹ + (1 − δ)]I}`. -/
def Assumption1 (P : Params) : Prop :=
  (2 - P.δ) * P.I < P.X ∧
  P.X < min (2 * P.I) (2 * ((1 + P.θbar)⁻¹ + (1 - P.δ)) * P.I)

/-- Assumption 2 (Bank Charter Value): `Y` increasing and concave on `[0, θ̄]`, differentiable
there (the paper's "smooth function of θ"), with (2) `Y′(θ̄) > 2(X − I + c)/(1 − θ̄)²` and
(3) `Y(0) < 2c`. `Y′` is the two-sided derivative `deriv P.Y`. -/
def Assumption2 (P : Params) : Prop :=
  MonotoneOn P.Y (Set.Icc 0 P.θbar) ∧
  ConcaveOn ℝ (Set.Icc 0 P.θbar) P.Y ∧
  (∀ θ ∈ Set.Icc 0 P.θbar, DifferentiableAt ℝ P.Y θ) ∧
  2 * (P.X - P.I + P.c) / (1 - P.θbar) ^ 2 < deriv P.Y P.θbar ∧
  P.Y 0 < 2 * P.c

/-- Assumption 3 (Screening Is Economically Valuable), display (4):
`X − I − c − ψ[2c − Y(0)] > 0`. -/
def Assumption3 (P : Params) : Prop :=
  0 < P.X - P.I - P.c - P.ψ * (2 * P.c - P.Y 0)

/-- Assumption 4, display (5):
`ψ[Y′(0) − 2(X − I + c)/(1 − θ̄)²] + 0.5Y′(0) ≤ X + 0.5[Y(0) + I]`. -/
def Assumption4 (P : Params) : Prop :=
  P.ψ * (deriv P.Y 0 - 2 * (P.X - P.I + P.c) / (1 - P.θbar) ^ 2) +
    (1 / 2 : ℝ) * deriv P.Y 0 ≤ P.X + (1 / 2 : ℝ) * (P.Y 0 + P.I)

/-- Assumption 5 (Matching Technology): `λ ∈ [0, 1]`; the meeting function itself is `alpha`. -/
def Assumption5 (P : Params) : Prop := 0 ≤ P.lam ∧ P.lam ≤ 1

/-- (8): the minimum equity inducing screening with the market closed,
`E^hom(θ) = (2θ(X − I) + 2c)/(1 − θ) − Y(θ)`. -/
noncomputable def Ehom (P : Params) (θ : ℝ) : ℝ :=
  (2 * θ * (P.X - P.I) + 2 * P.c) / (1 - θ) - P.Y θ

/-- (9): profit of a screening bank, `π^hom_s(θ) = X − I − ψE^hom(θ) − c`. -/
noncomputable def piS (P : Params) (θ : ℝ) : ℝ :=
  P.X - P.I - P.ψ * Ehom P θ - P.c

/-- (10): profit of a non-screening bank,
`π^hom_ns(θ) = [θ + 0.5(1 − θ)]X − I + θ(X − I) − 0.5(1 − θ)Y(θ)`. -/
noncomputable def piNS (P : Params) (θ : ℝ) : ℝ :=
  (θ + (1 / 2 : ℝ) * (1 - θ)) * P.X - P.I + θ * (P.X - P.I) -
    (1 / 2 : ℝ) * (1 - θ) * P.Y θ

/-- (11): the value added of screening, `∆π^hom(θ) = π^hom_s(θ) − π^hom_ns(θ)`. -/
noncomputable def dPi (P : Params) (θ : ℝ) : ℝ := piS P θ - piNS P θ

/-- (6): probability a seller meets a buyer, `α(n) = λn/(1 + n)`. -/
noncomputable def alpha (P : Params) (n : ℝ) : ℝ := P.lam * n / (1 + n)

/-- Probability a buyer meets a seller, the paper's `α(n)/n`, written `λ/(1 + n)` as in
Assumption 5; at `n = 0` it takes its limit value `λ`. -/
noncomputable def buyerMeet (P : Params) (n : ℝ) : ℝ := P.lam / (1 + n)

/-- The buyer's bargaining power `β = 1/(1 + n)` (Assumption 5). -/
noncomputable def beta (n : ℝ) : ℝ := 1 / (1 + n)

/-- (12): the Nash product `(X − p)^β (p − I)^{1−β}` (real powers). -/
noncomputable def nashProduct (P : Params) (n p : ℝ) : ℝ :=
  (P.X - p) ^ (beta n) * (p - P.I) ^ (1 - beta n)

/-- (13): the loan price `p = X − (X − I)/(1 + n)`. -/
noncomputable def price (P : Params) (n : ℝ) : ℝ :=
  P.X - (P.X - P.I) / (1 + n)

/-- (14): the buyer's equity with trading, `E^het(θ) = E^hom(θ) − λ(X − p)/(1 + n)`. -/
noncomputable def Ehet (P : Params) (θ n : ℝ) : ℝ :=
  Ehom P θ - P.lam * (P.X - price P n) / (1 + n)

/-- Left-hand side of the buyer's IC (A2) at equity `E` and deposits `D`:
`−E − ψE + 0.5(X − D + X − I) + 0.5E + 0.5(1 − θ)(α(n)/n)(X − p) − c`. -/
noncomputable def icLHS (P : Params) (θ n E D : ℝ) : ℝ :=
  -E - P.ψ * E + (1 / 2 : ℝ) * (P.X - D + P.X - P.I) +
    (1 / 2 : ℝ) * E + (1 / 2 : ℝ) * (1 - θ) * buyerMeet P n *
      (P.X - price P n) - P.c

/-- Right-hand side of (A2) and of (7):
`max{−ψE, −E − ψE + [θ + 0.5(1 − θ)](X − D + X − I) − 0.5(1 − θ)Y(θ)}`. -/
noncomputable def icRHS (P : Params) (θ E D : ℝ) : ℝ :=
  max (-P.ψ * E)
    (-E - P.ψ * E + (θ + (1 / 2 : ℝ) * (1 - θ)) *
      (P.X - D + P.X - P.I) - (1 / 2 : ℝ) * (1 - θ) * P.Y θ)

/-- A buyer's expected profit: the LHS of (A2) at `E = E^het`, `D = I − E^het`. -/
noncomputable def buyerProfit (P : Params) (θ n : ℝ) : ℝ :=
  icLHS P θ n (Ehet P θ n) (P.I - Ehet P θ n)

/-- A seller's expected profit: `π^hom_ns(θ) + 0.5(1 − θ)α(n)(p − I)`. -/
noncomputable def sellerProfit (P : Params) (θ n : ℝ) : ℝ :=
  piNS P θ + (1 / 2 : ℝ) * (1 - θ) * alpha P n * (price P n - P.I)

/-- A sole seller among buyers (`n ↑ ∞`, so `α → λ`, `p → X`):
`π^hom_ns(θ) + 0.5λ(1 − θ)(X − I)`. -/
noncomputable def soleSellerProfit (P : Params) (θ : ℝ) : ℝ :=
  piNS P θ + (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I)

/-- The left-hand side of (15): `λ(X − I)[(1 − θ)/2 · (n − 1)/(n + 1) − ψ/(n + 1)²]`. -/
noncomputable def eq15LHS (P : Params) (θ n : ℝ) : ℝ :=
  P.lam * (P.X - P.I) *
    ((1 - θ) / 2 * ((n - 1) / (n + 1)) - P.ψ / (n + 1) ^ 2)

/-- (A1): `0.5(1 − θ̄)X/(1 + 2ψ(1 − θ̄)⁻¹) − θ̄(X − I) + 0.5(1 − θ̄)Y(θ̄) < c
< 0.5X/(1 + 2ψ) + 0.5Y(0)`. -/
noncomputable def CondA1 (P : Params) : Prop :=
  (1 / 2 : ℝ) * (1 - P.θbar) * P.X /
      (1 + 2 * P.ψ / (1 - P.θbar)) - P.θbar * (P.X - P.I) +
      (1 / 2 : ℝ) * (1 - P.θbar) * P.Y P.θbar < P.c ∧
  P.c < (1 / 2 : ℝ) * P.X / (1 + 2 * P.ψ) + (1 / 2 : ℝ) * P.Y 0

/-- (A3): `∆π^hom(0) > 0.5λ(X − I)`. -/
noncomputable def CondA3 (P : Params) : Prop :=
  (1 / 2 : ℝ) * P.lam * (P.X - P.I) < dPi P 0

/-- (A6), sign-corrected: `∆π^hom(θ̄) < −0.5λ(1 − θ̄)(X − I) − ψλ(X − I)`, i.e. the sole
buyer's gain `∆π^hom(θ) + 0.5λ(1 − θ)(X − I) + ψλ(X − I)` is negative at `θ = θ̄`. The paper
prints `+ ψλ(X − I)` for the last term. -/
noncomputable def CondA6 (P : Params) : Prop :=
  dPi P P.θbar < -(1 / 2 : ℝ) * P.lam * (1 - P.θbar) * (P.X - P.I) -
    P.ψ * P.lam * (P.X - P.I)

/-- (A4) at `θ`: `−∆π^hom(θ) + 0.5λ(1 − θ)(X − I) = 0`. -/
noncomputable def CondA4 (P : Params) (θ : ℝ) : Prop :=
  -dPi P θ + (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I) = 0

/-- (A7) at `θ`: `∆π^hom(θ) + 0.5λ(1 − θ)(X − I) + ψλ(X − I) = 0`. -/
noncomputable def CondA7 (P : Params) (θ : ℝ) : Prop :=
  dPi P θ + (1 / 2 : ℝ) * P.lam * (1 - θ) * (P.X - P.I) +
    P.ψ * P.lam * (P.X - P.I) = 0

/-- The closed-market outcome in Proposition 1, reduced to its payoff comparison. `screens`
records the bank's screening choice and `E` its equity. At equal profits the paper selects
no screening (footnote 21); screening therefore requires a strict profit advantage. -/
noncomputable def IsClosedEquilibrium (P : Params) (θ : ℝ)
    (screens : Bool) (E : ℝ) : Prop :=
  (screens = true ∧ E = Ehom P θ ∧ 0 < E ∧ piNS P θ < piS P θ) ∨
  (screens = false ∧ E = 0 ∧ piS P θ ≤ piNS P θ)

/-- Equilibrium with the interbank market open, at boom probability `θ`, described by the
buyer share `s = N_b/N ∈ [0, 1]` (tightness `n = s/(1 − s)`). Buyers hold `E^het` and screen,
sellers hold no equity and do not screen (Lemma 1's proof); price is (13).
* `s = 1` (all screen): a sole seller (`n ↑ ∞`) does not gain over a screening bank;
* `s = 0` (none screens): a sole buyer (`n = 0`) does not gain over a non-screening bank;
* `0 < s < 1`: buyers and sellers earn the same, (A5)/(A8).
The corner conditions are weak inequalities. -/
noncomputable def IsEquilibrium (P : Params) (θ s : ℝ) : Prop :=
  0 ≤ s ∧ s ≤ 1 ∧
  (s = 1 → soleSellerProfit P θ ≤ piS P θ) ∧
  (s = 0 → buyerProfit P θ 0 ≤ piNS P θ) ∧
  (0 < s → s < 1 →
    buyerProfit P θ (s / (1 - s)) = sellerProfit P θ (s / (1 - s)))

end MarketFreeze.Hetero


