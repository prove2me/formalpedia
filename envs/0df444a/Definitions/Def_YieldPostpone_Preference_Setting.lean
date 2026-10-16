-- Prove2me | Definitions.Def_YieldPostpone_Preference_Setting
-- name    : YieldPostpone_Preference_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:23:47.189979+00:00
-- url     : https://prove2.me/theorems/f156a2b3-ba13-4a77-bcf4-ad6d2168c89e
-- title:
--   §3, pp. 7–10; App. B (3), PDF p. 33 — two-point yield, linear demand, the four Stackelberg games, subgame-perfect equilibrium, outcome (π_R, π_S, CS), thresholds
-- statement:
--   The supply-chain model of Geng, Guo, Xiao and Yang (§3, pp. 7–10, and Appendix B).
--
--   **Primitives.** A supplier sells to a retailer, who sells to a market with linear demand $d(p)=a-bp$, $a,b>0$ (inverse demand $p(t)=(a-t)/b$). Production is subject to a **two-point proportional yield**
--   $$Y=\begin{cases}1&\text{with probability }\theta,\\ \alpha&\text{with probability }1-\theta,\end{cases}\qquad \alpha,\theta\in(0,1),$$
--   with mean $\mu=\alpha(1-\theta)+\theta$. For a function $f$, $\mathbb E f(Y)=\theta f(1)+(1-\theta)f(\alpha)$. The supplier pays $c$ per unit of *planned* production $Q$. The standing ranges (3) are $0<c<a\mu/b$, retail prices $0<p<a/b$, and wholesale prices $c<w<a/b$ (pay-by-order) or $c/\mu<w<a/b$ (pay-by-delivery). The cost $c$ is an argument of every object, separate from the parameters $(a,b,\alpha,\theta)$.
--
--   **Scenarios.** OA, OR, DA, DR: payment by **O**rdered or **D**elivered quantity, and ex **A**nte or **R**esponsive pricing. With an order $q$ and production $Q$, the delivered quantity is $\hat q=\min\{YQ,q\}$, the transfer is $T=wq$ (pay-by-order) or $T=w\min\{YQ,q\}$ (pay-by-delivery), and sales revenue at price $p$ with $x$ units available is $p\min\{d(p),x\}$. The supplier's production-stage profit is $\mathbb E[T]-cQ$.
--
--   **Timing** (Table 1): the supplier sets $w$; the retailer orders $q$ (and, ex ante, commits to $p$); the supplier chooses $Q$ (equal to $q$ under pay-by-order); the yield realizes and $\hat q$ is delivered; under responsive pricing the retailer then sets $p$ knowing $\hat q$.
--
--   **Strategy profiles and equilibrium.** A profile $\sigma$ consists of a wholesale price $w$, a production rule $Q(w,q)$, an order rule $q(w)$, an ex ante price rule $p(w)$ and an ex post price rule $p^{\mathrm r}(w,q,x)$. It is a **subgame-perfect equilibrium** of scenario $k$ at cost $c$ when:
--
--   1. *Production.* Under pay-by-order $Q(w,q)=q$. Under pay-by-delivery, for every admissible $w$ and every order $q\ge0$, $Q(w,q)\ge0$ maximizes the supplier's expected profit over $Q'\ge0$, and $Q(w,q)=q$ whenever $Q'=q$ is itself a maximizer.
--   2. *Ex post price* (OR, DR). For all $w,q$ and every delivery $x\ge0$, $p^{\mathrm r}(w,q,x)$ is an admissible price maximizing $p\min\{d(p),x\}$.
--   3. *Retailer.* For every admissible $w$, the order $q(w)\ge0$ (and, ex ante, the admissible price $p(w)$) maximizes the retailer's expected profit $\mathbb E[\text{revenue}-T]$ over all orders $q'\ge0$ (and admissible prices $p'$), given the production rule and, under responsive pricing, the ex post price rule.
--   4. *Supplier.* $w$ is admissible and maximizes the supplier's expected profit, anticipating $q(\cdot)$ and $Q(\cdot,\cdot)$, over all admissible wholesale prices.
--
--   **Outcomes.** $\pi^k_R$ and $\pi^k_S$ are the retailer's and supplier's expected profits on the equilibrium path. With consumer surplus
--   $$\mathcal S(p,X)=\int_0^{\min\{d(p),X\}}\big(p(t)-p\big)\,dt,$$
--   $CS^k=\mathbb E\,\mathcal S(p,\hat q)$ on the path, where $p$ is the ex post price at $\hat q$ under responsive pricing (OR, DR) and the committed price under ex ante pricing (OA, DA).
--
--   **Thresholds** (functions of $(a,b,\alpha,\theta)$; Appendices B–C):
--   $$c^{OA}_1=\frac{a\alpha(\mu-\alpha\theta-2\theta\sqrt\mu)}{b(\alpha+\theta)},\quad \hat w=c^{DA}=\frac{a\alpha(\mu-\theta\sqrt\mu)}{b(\alpha+\theta)},\quad c^{OR}=\frac ab\alpha(1-\theta)\Big((1-\alpha)-\sqrt{\alpha^2+\tfrac{\theta}{1-\theta}}\Big),$$
--   $$c^{DR}_1=\frac{a\alpha(1-\theta)\big(\mu^2+\theta-2\theta\sqrt{\alpha\mu(1-\alpha)(1-\theta)}\big)}{b\big(\alpha^2(1-\theta)^3+4\alpha\theta(1-\theta)+\theta(1+\theta)^2\big)},\quad c^{DR}_2=\frac{a\alpha\mu(1-\theta)}{b(\mu+\theta)},\quad \tilde C=\frac{a\alpha\big(1-\sqrt{\alpha^2(1-\theta)+\theta}\big)}{b(1+\alpha)},$$
--   $\bar C=\frac{a\alpha}{b}\cdot\frac{\varphi_a-\theta\mu\sqrt{\varphi_c}}{\varphi_b}$ of (8), $\Theta(\alpha)$ of PDF p. 39, $\theta_1(\alpha)=\frac{1-4\alpha+\sqrt{1+8\alpha}}{8(1-\alpha)}$, $\theta_2(\alpha)$ the largest real root of $-\alpha^3+\alpha^2(5+\alpha)x+(16-19\alpha-6\alpha^2)x^2-25(1-\alpha)x^3$, the regions $H_1=\{0<\theta<\theta_1\}$, $H_2=\{\theta_1<\theta<\theta_2\}$, $H_3=\{\theta_2<\theta<1\}$, and $c^{OA}_2$, the larger root in $c$ of $\alpha^2(a\mu-bc)^2=4b\mu(a\alpha-b\hat w)(\hat w-c)$.
--
--   These objects are shared by every statement of the missions built on this setting: the equilibrium profits and consumer surpluses compared in Propositions 1–5 are outcomes of subgame-perfect equilibria of these games, not closed-form expressions, and the closed forms of Lemmas 1–4 are theorems about them.
--
--   **Formalization Note** Strategies are functions of everything observed before the move, and optimality is required at every admissible history, on and off the path. The tie rule in clause 1 is a series convention: at $w=c/(\alpha(1-\theta))$ the supplier is indifferent among all $Q\in[q,q/\alpha]$, and (4) assigns the tie to inflation; with that assignment scenario DR has no equilibrium for $c^{DR}_1<c<c^{DR}_2$, while Lemma 4's profits there are those of the equilibrium with $Q=q$. Display (2), p. 10, prints the price labels of $CS$ swapped; the reading used here is the one of the Appendix B summaries. $c^{OA}_2$ is defined as the larger root of the quadratic above, which coincides numerically with "the second root" of the quartic printed on PDF p. 34; $\theta_2$ is defined as the supremum of the root set, i.e. the largest real root ("the third root"). `Real.sqrt` returns $0$ on negative arguments; every radicand above is nonnegative under the standing ranges ($\mu\ge0$, $\alpha\mu(1-\alpha)(1-\theta)\ge0$, $\alpha^2(1-\theta)+\theta\ge0$, $\varphi_c\ge0$, $\alpha(3+5\alpha+\alpha^2)\ge0$, $1+8\alpha\ge0$); the discriminant inside $c^{OA}_2$ is not covered by this argument and is positive on every parameter point checked numerically. $\hat w$ and $c^{DA}$ are the same expression; both names are kept because the paper uses both (App. B.1 and B.3). The symbol $\hat w$ of App. B.2 (a different wholesale-price threshold) is not defined here. Every threshold is defined for all parameter values but carries the paper's meaning only under the standing ranges $a,b>0$, $\alpha,\theta\in(0,1)$, which the statements using them assume.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version, sha256 7cfc7261…), pp. 7–10, (1)–(2), Table 1; App. A–B, PDF pp. 33–34 (appendix pp. 1–2), (3)–(5); App. B–C, PDF pp. 34–39 (appendix pp. 2–7), thresholds and (6), (8)

import Mathlib

namespace YieldPostpone.Preference

/-- Model parameters: demand intercept `a`, demand slope `b`, low yield level `α`,
probability `θ` of full yield. The production cost `c` is kept separate. -/
structure Params where
  a : ℝ
  b : ℝ
  α : ℝ
  θ : ℝ

/-- Expected yield factor `μ = α(1 − θ) + θ`. -/
def μ (P : Params) : ℝ := P.α * (1 - P.θ) + P.θ

/-- Standing parameter ranges, (1) and Table 2: `a, b > 0`, `α, θ ∈ (0, 1)`. -/
def Params.Valid (P : Params) : Prop :=
  0 < P.a ∧ 0 < P.b ∧ 0 < P.α ∧ P.α < 1 ∧ 0 < P.θ ∧ P.θ < 1

/-- Expectation over the two-point yield (1): `Y = 1` w.p. `θ`, `Y = α` w.p. `1 − θ`. -/
def E (P : Params) (f : ℝ → ℝ) : ℝ := P.θ * f 1 + (1 - P.θ) * f P.α

/-- Linear demand `d(p) = a − b p`. -/
def demand (P : Params) (p : ℝ) : ℝ := P.a - P.b * p

/-- The four scenarios: pay-by-Order / pay-by-Delivery × ex Ante / Responsive pricing. -/
inductive Scenario
  | OA
  | OR
  | DA
  | DR
  deriving DecidableEq, Repr

/-- Pay-by-delivery scenarios (DA, DR). -/
def Scenario.byDelivery : Scenario → Bool
  | .OA => false
  | .OR => false
  | .DA => true
  | .DR => true

/-- Responsive (ex post) pricing scenarios (OR, DR). -/
def Scenario.responsive : Scenario → Bool
  | .OA => false
  | .OR => true
  | .DA => false
  | .DR => true

/-- Delivered quantity `q̂ = min{y Q, q}` at yield realization `y`. -/
def delivered (y Q q : ℝ) : ℝ := min (y * Q) q

/-- Transfer payment `T^k` at yield realization `y`: `w q` (pay-by-order) or
`w min{y Q, q}` (pay-by-delivery). -/
def transfer (k : Scenario) (w Q q y : ℝ) : ℝ :=
  if k.byDelivery then w * min (y * Q) q else w * q

/-- Supplier's expected profit at the production stage: `E[T^k(w, Q, q)] − c Q`. -/
def supplierProfit (P : Params) (c : ℝ) (k : Scenario) (w Q q : ℝ) : ℝ :=
  E P (transfer k w Q q) - c * Q

/-- Admissible wholesale prices (3): `c < w < a/b` (pay-by-order),
`c/μ < w < a/b` (pay-by-delivery). -/
def wAdm (P : Params) (c : ℝ) (k : Scenario) (w : ℝ) : Prop :=
  (if k.byDelivery then c / μ P < w else c < w) ∧ w < P.a / P.b

/-- Admissible retail prices (3): `0 < p < a/b`. -/
def pAdm (P : Params) (p : ℝ) : Prop := 0 < p ∧ p < P.a / P.b

/-- Sales revenue `p min{d(p), x}` with `x` units available for sale. -/
def salesRev (P : Params) (p x : ℝ) : ℝ := p * min (demand P p) x

/-- A strategy profile. Strategies are functions of everything observed before the move.
* `w`  : the supplier's wholesale price;
* `Q w q` : the supplier's production after `(w, q)`;
* `q w` : the retailer's order after `w`;
* `p w` : the retailer's ex ante retail price after `w` (used in OA, DA);
* `pr w q x` : the retailer's ex post retail price after `(w, q)` and delivery `x`
  (used in OR, DR). -/
structure Profile where
  w : ℝ
  Q : ℝ → ℝ → ℝ
  q : ℝ → ℝ
  p : ℝ → ℝ
  pr : ℝ → ℝ → ℝ → ℝ

/-- Retailer's expected profit after wholesale price `w` when it orders `q'` and (ex ante)
commits to price `p'`; production follows `σ.Q`, and under responsive pricing the price is
`σ.pr` at the delivered quantity (then `p'` is ignored). -/
def retailerProfit (P : Params) (k : Scenario) (σ : Profile) (w q' p' : ℝ) : ℝ :=
  E P (fun y =>
    (if k.responsive then
        salesRev P (σ.pr w q' (delivered y (σ.Q w q') q')) (delivered y (σ.Q w q') q')
      else salesRev P p' (delivered y (σ.Q w q') q'))
      - transfer k w (σ.Q w q') q' y)

/-- Supplier's expected profit from wholesale price `w`, anticipating `σ.q` and `σ.Q`. -/
def supplierValue (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) (w : ℝ) : ℝ :=
  supplierProfit P c k w (σ.Q w (σ.q w)) (σ.q w)

/-- Subgame-perfect equilibrium of the Stackelberg game of scenario `k` at cost `c`
(Table 1, p. 9, (3)). Optimality is required in every subgame.
1. Production. Pay-by-order: `Q = q`. Pay-by-delivery: for every admissible `w` and every
   order `q ≥ 0`, `σ.Q w q ≥ 0` maximizes the supplier's profit over `Q' ≥ 0`, and
   `σ.Q w q = q` whenever `Q' = q` is itself a maximizer (tie rule).
2. Ex post price (responsive `k`): for all `w, q` and every delivery `x ≥ 0`, `σ.pr w q x` is
   an admissible price maximizing `p min{d(p), x}` over admissible prices.
3. Retailer: for every admissible `w`, the order `σ.q w ≥ 0` (and, ex ante, the admissible
   price `σ.p w`) maximizes the retailer's expected profit over `q' ≥ 0` (and admissible `p'`).
4. Supplier: `σ.w` is admissible and maximizes `supplierValue` over admissible `w'`. -/
def IsSPE (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) : Prop :=
  (k.byDelivery = false → ∀ w q : ℝ, σ.Q w q = q) ∧
  (k.byDelivery = true → ∀ w q : ℝ, wAdm P c k w → 0 ≤ q →
      0 ≤ σ.Q w q ∧
      (∀ Q' : ℝ, 0 ≤ Q' → supplierProfit P c k w Q' q ≤ supplierProfit P c k w (σ.Q w q) q) ∧
      ((∀ Q' : ℝ, 0 ≤ Q' → supplierProfit P c k w Q' q ≤ supplierProfit P c k w q q) →
        σ.Q w q = q)) ∧
  (k.responsive = true → ∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧
      ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x) ∧
  (∀ w : ℝ, wAdm P c k w →
      0 ≤ σ.q w ∧ (k.responsive = false → pAdm P (σ.p w)) ∧
      ∀ q' p' : ℝ, 0 ≤ q' → (k.responsive = false → pAdm P p') →
        retailerProfit P k σ w q' p' ≤ retailerProfit P k σ w (σ.q w) (σ.p w)) ∧
  wAdm P c k σ.w ∧
  ∀ w' : ℝ, wAdm P c k w' → supplierValue P c k σ w' ≤ supplierValue P c k σ σ.w

/-- Retailer's equilibrium expected profit `π^k_R` of profile `σ`. -/
def piR (P : Params) (_c : ℝ) (k : Scenario) (σ : Profile) : ℝ :=
  retailerProfit P k σ σ.w (σ.q σ.w) (σ.p σ.w)

/-- Supplier's equilibrium expected profit `π^k_S` of profile `σ`. -/
def piS (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) : ℝ :=
  supplierValue P c k σ σ.w

/-- Consumer surplus `S(p, X) = ∫₀^{min{d(p), X}} (p(t) − p) dt`, `p(t) = (a − t)/b`. -/
noncomputable def surplus (P : Params) (p X : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(min (demand P p) X), ((P.a - t) / P.b - p)

/-- Expected consumer surplus `CS^k` on the path of `σ`: the ex post price at the delivered
quantity under responsive pricing (OR, DR), the committed price under ex ante pricing (OA, DA). -/
noncomputable def CS (P : Params) (_c : ℝ) (k : Scenario) (σ : Profile) : ℝ :=
  E P (fun y =>
    surplus P
      (if k.responsive then
          σ.pr σ.w (σ.q σ.w) (delivered y (σ.Q σ.w (σ.q σ.w)) (σ.q σ.w))
        else σ.p σ.w)
      (delivered y (σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)))

/-! ### Thresholds (functions of `(a, b, α, θ)` only) -/

/-- `c^OA_1 = aα(μ − αθ − 2θ√μ) / (b(α + θ))`, App. B.1, PDF p. 34. -/
noncomputable def cOA1 (P : Params) : ℝ :=
  P.a * P.α * (μ P - P.α * P.θ - 2 * P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ))

/-- `ŵ = aα(μ − θ√μ) / (b(α + θ))`, App. B.1, PDF pp. 34–35. -/
noncomputable def what (P : Params) : ℝ :=
  P.a * P.α * (μ P - P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ))

/-- `c^OA_2`: the larger root in `c` of `α²(aμ − bc)² = 4bμ(aα − bŵ)(ŵ − c)`
(series convention for "the second root of the polynomial", PDF p. 34), by the quadratic
formula for `A c² + B c + C = 0`. -/
noncomputable def cOA2 (P : Params) : ℝ :=
  let K := P.a * P.α - P.b * what P
  let A := P.α ^ 2 * P.b ^ 2
  let B := -2 * P.α ^ 2 * P.a * P.b * μ P + 4 * P.b * μ P * K
  let C := P.α ^ 2 * P.a ^ 2 * μ P ^ 2 - 4 * P.b * μ P * K * what P
  (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A)

/-- `c^OR = (a/b) α(1 − θ)((1 − α) − √(α² + θ/(1 − θ)))`, App. B.2, PDF p. 35. -/
noncomputable def cOR (P : Params) : ℝ :=
  P.a / P.b * P.α * (1 - P.θ) * ((1 - P.α) - Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)))

/-- `c^DA = aα(μ − θ√μ) / (b(α + θ))`, App. B.3, PDF p. 36. -/
noncomputable def cDA (P : Params) : ℝ :=
  P.a * P.α * (μ P - P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ))

/-- `c^DR_1`, App. B.4, PDF p. 37. -/
noncomputable def cDR1 (P : Params) : ℝ :=
  P.a * P.α * (1 - P.θ) *
      (μ P ^ 2 + P.θ - 2 * P.θ * Real.sqrt (P.α * μ P * (1 - P.α) * (1 - P.θ))) /
    (P.b * (P.α ^ 2 * (1 - P.θ) ^ 3 + 4 * P.α * P.θ * (1 - P.θ) + P.θ * (1 + P.θ) ^ 2))

/-- `c^DR_2 = aαμ(1 − θ) / (b(μ + θ))`, App. B.4, PDF p. 37. -/
noncomputable def cDR2 (P : Params) : ℝ :=
  P.a * P.α * μ P * (1 - P.θ) / (P.b * (μ P + P.θ))

/-- `C̃ = aα(1 − √(α²(1 − θ) + θ)) / (b(1 + α))`, (6), PDF p. 37. -/
noncomputable def Ctil (P : Params) : ℝ :=
  P.a * P.α * (1 - Real.sqrt (P.α ^ 2 * (1 - P.θ) + P.θ)) / (P.b * (1 + P.α))

/-- `C̄ = (aα/b)(φ_a − θμ√φ_c)/φ_b`, (8), PDF p. 38. -/
noncomputable def Cbar (P : Params) : ℝ :=
  let φa := P.α * (1 - P.θ) * (P.α - P.α ^ 2 * (1 - P.θ) + 2 * P.θ * (1 - P.α)) + P.θ ^ 2
  let φb := φa + P.α * P.θ * (P.α + μ P * (1 - P.α))
  let φc := P.α * (1 - P.θ) * (2 - P.α) + P.θ
  P.a * P.α / P.b * ((φa - P.θ * μ P * Real.sqrt φc) / φb)

/-- `Θ(α) = α(3(1 − α − 4α²) + 4√(α(3 + 5α + α²))) / ((1 − α)(3 + 4α)²)`, PDF p. 39. -/
noncomputable def Theta (α : ℝ) : ℝ :=
  α * (3 * (1 - α - 4 * α ^ 2) + 4 * Real.sqrt (α * (3 + 5 * α + α ^ 2))) /
    ((1 - α) * (3 + 4 * α) ^ 2)

/-- `θ₁(α) = (1 − 4α + √(1 + 8α)) / (8(1 − α))`, PDF p. 34. -/
noncomputable def theta1 (α : ℝ) : ℝ :=
  (1 - 4 * α + Real.sqrt (1 + 8 * α)) / (8 * (1 - α))

/-- `θ₂(α)`: the largest real root of
`−α³ + α²(5 + α)x + (16 − 19α − 6α²)x² − 25(1 − α)x³` (PDF p. 34, "the third root"). -/
noncomputable def theta2 (α : ℝ) : ℝ :=
  sSup {x : ℝ | -α ^ 3 + α ^ 2 * (5 + α) * x + (16 - 19 * α - 6 * α ^ 2) * x ^ 2
      - 25 * (1 - α) * x ^ 3 = 0}

/-- Region `H₁ = {θ < θ₁(α)}`, PDF p. 34. -/
def H1 (α θ : ℝ) : Prop := 0 < θ ∧ θ < theta1 α

/-- Region `H₂ = {θ₁(α) < θ < θ₂(α)}`, PDF p. 34. -/
def H2 (α θ : ℝ) : Prop := theta1 α < θ ∧ θ < theta2 α

/-- Region `H₃ = {θ₂(α) < θ < 1}`, PDF p. 34. -/
def H3 (α θ : ℝ) : Prop := theta2 α < θ ∧ θ < 1

end YieldPostpone.Preference


