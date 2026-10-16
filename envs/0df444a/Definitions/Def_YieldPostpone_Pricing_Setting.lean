-- Prove2me | Definitions.Def_YieldPostpone_Pricing_Setting
-- name    : YieldPostpone_Pricing_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:23:52.066432+00:00
-- url     : https://prove2.me/theorems/ccf301a1-454a-42c5-b69c-07b2a3696825
-- title:
--   §3, pp. 7–10; App. B (3), PDF p. 33 — two-point yield, linear demand, the four Stackelberg games, subgame-perfect equilibrium, outcome (π_R, π_S, CS), thresholds
-- statement:
--   This file sets up the model of Geng, Guo, Xiao and Yang, *Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?*, §3 (pp. 7–10) and Appendix B.
--
--   **Parameters.** A supplier sells to a retailer, who sells to a market with linear demand $d(p) = a - bp$, $a, b > 0$, and inverse demand $p(t) = (a-t)/b$. The supplier pays a unit cost $c$ on its *planned* production $Q$, but only a random fraction $Y$ of it is realized:
--   $$Y = \begin{cases} 1 & \text{with probability } \theta,\\ \alpha & \text{with probability } 1-\theta,\end{cases}\qquad \alpha,\theta\in(0,1),\qquad \mu = \alpha(1-\theta)+\theta .$$
--   Expectations are the two-point sums $\mathbb E f(Y) = \theta f(1) + (1-\theta) f(\alpha)$. The cost $c$ is kept as a separate argument; the standing range (3) is $0 < c < a\mu/b$.
--
--   **The four scenarios.** The retailer orders $q$ and receives $\hat q = \min\{YQ, q\}$. It pays either for the ordered quantity, $T = wq$ (*pay-by-order*, O), or for the delivered quantity, $T = w\min\{YQ,q\}$ (*pay-by-delivery*, D). It either commits to a retail price $p$ with its order (*ex ante pricing*, A), or sets the price after seeing $\hat q$ (*responsive pricing*, R). Its sales revenue with $x$ units at price $p$ is $p\min\{d(p), x\}$. This gives scenarios OA, OR, DA, DR. In each, the supplier sets $w$; the retailer orders $q$ (and, ex ante, sets $p$); the supplier chooses $Q$ (under pay-by-order $Q = q$, as the model prescribes); the yield realizes; and under responsive pricing the retailer then sets $p$. The supplier's expected profit is $\mathbb E[T] - cQ$; the retailer's is the expected revenue minus $\mathbb E[T]$.
--
--   **Admissible actions** (3): $c < w < a/b$ under pay-by-order and $c/\mu < w < a/b$ under pay-by-delivery; $0 < p < a/b$; $q \ge 0$; $Q \ge 0$.
--
--   **Subgame-perfect equilibrium.** A strategy profile $\sigma$ consists of a wholesale price $w$, a production rule $Q(w,q)$, an order rule $q(w)$, an ex ante price rule $p(w)$ and an ex post price rule $p^{\mathrm{post}}(w,q,x)$. It is a subgame-perfect equilibrium of scenario $k$ when:
--   1. under pay-by-order $Q(w,q) = q$; under pay-by-delivery, for every admissible $w$ and every $q \ge 0$, $Q(w,q) \ge 0$ maximizes the supplier's expected profit over all $Q' \ge 0$, and $Q(w,q) = q$ whenever $q$ is itself a maximizer;
--   2. under responsive pricing, for every $w$, $q$ and every available quantity $x \ge 0$, $p^{\mathrm{post}}(w,q,x)$ is an admissible price maximizing $p\min\{d(p),x\}$;
--   3. for every admissible $w$, $q(w) \ge 0$ (and, ex ante, $p(w)$ is admissible), and $(q(w), p(w))$ maximizes the retailer's expected profit over all $q' \ge 0$ (and admissible $p'$), with production and ex post pricing following $\sigma$;
--   4. $w$ is admissible and maximizes the supplier's expected profit, anticipating $q(\cdot)$ and $Q(\cdot,\cdot)$, over all admissible wholesale prices.
--
--   **Outcome.** $\pi^k_R$ and $\pi^k_S$ are the retailer's and the supplier's expected profits along the equilibrium path. With the consumer surplus
--   $$\mathcal S(p, X) = \int_0^{\min\{d(p),X\}} \big(p(t) - p\big)\,dt,$$
--   $CS^k = \mathbb E\,\mathcal S(p, \hat q)$, where $p$ is the ex post price at $\hat q$ under responsive pricing (OR, DR) and the committed price under ex ante pricing (OA, DA).
--
--   **Thresholds** (functions of $a, b, \alpha, \theta$ only):
--   - $c^{OA}_1 = \dfrac{a\alpha(\mu-\alpha\theta-2\theta\sqrt\mu)}{b(\alpha+\theta)}$ and $\hat w = c^{DA} = \dfrac{a\alpha(\mu-\theta\sqrt\mu)}{b(\alpha+\theta)}$ (App. B.1, B.3);
--   - $c^{OA}_2$: the larger root in $c$ of $\alpha^2(a\mu-bc)^2 = 4b\mu(a\alpha-b\hat w)(\hat w-c)$;
--   - $c^{OR} = \dfrac ab\,\alpha(1-\theta)\Big((1-\alpha) - \sqrt{\alpha^2 + \tfrac{\theta}{1-\theta}}\Big)$ (App. B.2);
--   - $c^{DR}_1 = \dfrac{a\alpha(1-\theta)\big(\mu^2+\theta-2\theta\sqrt{\alpha\mu(1-\alpha)(1-\theta)}\big)}{b\big(\alpha^2(1-\theta)^3+4\alpha\theta(1-\theta)+\theta(1+\theta)^2\big)}$ and $c^{DR}_2 = \dfrac{a\alpha\mu(1-\theta)}{b(\mu+\theta)}$ (App. B.4);
--   - $\tilde C = \dfrac{a\alpha\big(1-\sqrt{\alpha^2(1-\theta)+\theta}\big)}{b(1+\alpha)}$ (6), and $\bar C$ (8) (App. C);
--   - $\Theta(\alpha) = \dfrac{\alpha\big(3(1-\alpha-4\alpha^2) + 4\sqrt{\alpha(3+5\alpha+\alpha^2)}\big)}{(1-\alpha)(3+4\alpha)^2}$ (App. C, p. 39);
--   - $\theta_1(\alpha) = \dfrac{1-4\alpha+\sqrt{1+8\alpha}}{8(1-\alpha)}$, $\theta_2(\alpha)$ the largest real root of $-\alpha^3+\alpha^2(5+\alpha)x+(16-19\alpha-6\alpha^2)x^2-25(1-\alpha)x^3$, and the regions $\mathcal H_1 = \{\theta<\theta_1\}$, $\mathcal H_2 = \{\theta_1<\theta<\theta_2\}$, $\mathcal H_3 = \{\theta_2<\theta<1\}$ (App. B.1).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Strategies are functions of everything observed before the move, so optimality is required in every subgame, on and off the equilibrium path. When the supplier is indifferent between producing $q$ and inflating, the equilibrium requires $Q = q$; the paper's (4) assigns that tie to inflation, under which scenario DR has no equilibrium for $c^{DR}_1 < c < c^{DR}_2$, while the paper's own profits of Lemma 4 on that interval are those of the no-inflation tie. Display (2) on p. 10 prints the two price labels swapped; the surplus here uses the ex post price for OR/DR and the committed price for OA/DA, as Appendix B does. $c^{OA}_2$ is printed as "the second root" of a quartic, which is the product of the quadratic above and its conjugate under $\sqrt\mu\mapsto-\sqrt\mu$; the larger root of the quadratic is used (numerically equal to the quartic's second root). The radicands of all square roots are nonnegative for admissible parameters. Unused fields of a profile are ignored in scenarios that do not use them.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), pp. 7–10, (1)–(2), Table 1; App. B, PDF pp. 33–34 (appendix pp. 1–2), (3)–(5); App. B–C, PDF pp. 34–39 (appendix pp. 2–7), thresholds c^OA_1, ŵ, c^OA_2, c^OR, c^DA, c^DR_1, c^DR_2, (6), (8), Θ(α), θ₁, θ₂, H₁–H₃

import Mathlib

namespace YieldPostpone.Pricing

/-- Model parameters (§3.1, p. 7): market size `a`, price sensitivity `b`, yield fraction `α`
under yield loss, probability `θ` of full yield. The production cost `c` is a separate argument. -/
structure Params where
  a : ℝ
  b : ℝ
  α : ℝ
  θ : ℝ

/-- Expected yield factor `μ = α(1 − θ) + θ` (p. 7). -/
def μ (P : Params) : ℝ := P.α * (1 - P.θ) + P.θ

/-- Standing parameter ranges (1) and Table 2: `a, b > 0`, `α, θ ∈ (0, 1)`. -/
def Params.Valid (P : Params) : Prop :=
  0 < P.a ∧ 0 < P.b ∧ 0 < P.α ∧ P.α < 1 ∧ 0 < P.θ ∧ P.θ < 1

/-- Expectation over the two-point yield (1): `Y = 1` w.p. `θ`, `Y = α` w.p. `1 − θ`. -/
def E (P : Params) (f : ℝ → ℝ) : ℝ := P.θ * f 1 + (1 - P.θ) * f P.α

/-- Linear demand `d(p) = a − bp` (p. 7). -/
def demand (P : Params) (p : ℝ) : ℝ := P.a - P.b * p

/-- The four scenarios (p. 8): payment by Order / by Delivery, pricing ex Ante / Responsive. -/
inductive Scenario
  | OA
  | OR
  | DA
  | DR
  deriving DecidableEq

/-- Pay-by-delivery scenarios (DA, DR). -/
def Scenario.byDelivery : Scenario → Bool
  | .DA => true
  | .DR => true
  | _ => false

/-- Responsive (ex post) pricing scenarios (OR, DR). -/
def Scenario.responsive : Scenario → Bool
  | .OR => true
  | .DR => true
  | _ => false

/-- Delivered quantity `q̂ = min{yQ, q}` at yield realization `y` (p. 8). -/
def delivered (y Q q : ℝ) : ℝ := min (y * Q) q

/-- Transfer payment `T^k` at yield `y` (p. 9): `w·q` under pay-by-order, `w·min{yQ, q}` under
pay-by-delivery. -/
def transfer (k : Scenario) (w Q q y : ℝ) : ℝ :=
  if k.byDelivery then w * delivered y Q q else w * q

/-- Supplier's expected profit `E[T^k] − cQ` for wholesale price `w`, production `Q`, order `q`
(p. 9). -/
def supplierProfit (P : Params) (c : ℝ) (k : Scenario) (w Q q : ℝ) : ℝ :=
  E P (transfer k w Q q) - c * Q

/-- Admissible wholesale prices (3), PDF p. 33: `c < w < a/b` under pay-by-order and
`c/μ < w < a/b` under pay-by-delivery. -/
def wAdm (P : Params) (c : ℝ) (k : Scenario) (w : ℝ) : Prop :=
  (if k.byDelivery then c / μ P < w else c < w) ∧ w < P.a / P.b

/-- Admissible retail prices (3): `0 < p < a/b`. -/
def pAdm (P : Params) (p : ℝ) : Prop := 0 < p ∧ p < P.a / P.b

/-- Sales revenue `p · min{d(p), x}` when `x` units are available for sale (p. 9). -/
def salesRev (P : Params) (p x : ℝ) : ℝ := p * min (demand P p) x

/-- A strategy profile, common to all four scenarios (fields a scenario does not use are
ignored). Strategies are functions of everything observed before the move. -/
structure Profile where
  /-- supplier's wholesale price -/
  w : ℝ
  /-- supplier's production as a function of `(w, q)` -/
  Q : ℝ → ℝ → ℝ
  /-- retailer's order as a function of `w` -/
  q : ℝ → ℝ
  /-- retailer's ex ante retail price as a function of `w` (OA, DA) -/
  p : ℝ → ℝ
  /-- retailer's ex post retail price as a function of `(w, q, delivered quantity)` (OR, DR) -/
  pr : ℝ → ℝ → ℝ → ℝ

/-- Retailer's expected profit at wholesale price `w` when it orders `q'` and (ex ante) commits
to price `p'`; the production and the ex post price follow the profile `σ` (p. 9). -/
def retailerProfit (P : Params) (k : Scenario) (σ : Profile) (w q' p' : ℝ) : ℝ :=
  E P (fun y =>
    let x := delivered y (σ.Q w q') q'
    (if k.responsive then salesRev P (σ.pr w q' x) x else salesRev P p' x)
      - transfer k w (σ.Q w q') q' y)

/-- Supplier's expected profit from wholesale price `w`, anticipating the retailer's order and
its own production response in `σ` (p. 9). -/
def supplierValue (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) (w : ℝ) : ℝ :=
  supplierProfit P c k w (σ.Q w (σ.q w)) (σ.q w)

/-- Subgame-perfect equilibrium of scenario `k` (pp. 9–10, backward induction): optimality of
every move in every subgame.
1. Production: under pay-by-order `Q = q`; under pay-by-delivery, for every admissible `w` and
   every order `q ≥ 0`, `Q(w, q) ≥ 0` maximizes the supplier's profit over `Q' ≥ 0`, and equals
   `q` whenever `q` is itself a maximizer (tie rule: no inflation when indifferent).
2. Ex post price (responsive scenarios): for every `w`, `q` and delivered `x ≥ 0`, the price is
   admissible and maximizes `p · min{d(p), x}` over admissible prices.
3. Retailer: for every admissible `w`, the order is `≥ 0`, the ex ante price (if any) admissible,
   and they maximize the retailer's expected profit over all orders `q' ≥ 0` (and admissible
   ex ante prices `p'`).
4. Supplier: `σ.w` is admissible and maximizes `supplierValue` over admissible prices. -/
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

/-- Retailer's equilibrium expected profit `π^k_R` of the profile `σ`. -/
def piR (P : Params) (k : Scenario) (σ : Profile) : ℝ :=
  retailerProfit P k σ σ.w (σ.q σ.w) (σ.p σ.w)

/-- Supplier's equilibrium expected profit `π^k_S` of the profile `σ`. -/
def piS (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) : ℝ :=
  supplierValue P c k σ σ.w

/-- Consumer surplus `𝒮(p, X) = ∫₀^{min{d(p), X}} (p(t) − p) dt` with inverse demand
`p(t) = (a − t)/b` (p. 10). -/
noncomputable def surplus (P : Params) (p X : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(min (demand P p) X), ((P.a - t) / P.b - p)

/-- Expected consumer surplus `CS^k` of the profile `σ` (p. 10, (2)); the market price is the
ex post price at the delivered quantity under responsive pricing (OR, DR) and the committed
ex ante price otherwise (OA, DA). -/
noncomputable def CS (P : Params) (k : Scenario) (σ : Profile) : ℝ :=
  E P (fun y =>
    let w := σ.w
    let q := σ.q w
    let x := delivered y (σ.Q w q) q
    surplus P (if k.responsive then σ.pr w q x else σ.p w) x)

/-- The equilibrium outcome triple `(π^k_R, π^k_S, CS^k)`. -/
noncomputable def outcome (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) : ℝ × ℝ × ℝ :=
  (piR P k σ, piS P c k σ, CS P k σ)

/-! ### Thresholds (Appendices B and C). All depend on `(a, b, α, θ)` only. -/

/-- `c^OA_1` (App. B.1, PDF p. 34). -/
noncomputable def cOA1 (P : Params) : ℝ :=
  P.a * P.α * (μ P - P.α * P.θ - 2 * P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ))

/-- `ŵ` (App. B.1, PDF pp. 34–35). -/
noncomputable def what (P : Params) : ℝ :=
  P.a * P.α * (μ P - P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ))

/-- `c^OA_2`: the larger root in `c` of `α²(aμ − bc)² = 4bμ(aα − bŵ)(ŵ − c)`, by the quadratic
formula (series convention for "the second root of the polynomial", App. B.1, PDF p. 34). -/
noncomputable def cOA2 (P : Params) : ℝ :=
  let K := P.a * P.α - P.b * what P
  let A := P.α ^ 2 * P.b ^ 2
  let B := -2 * P.α ^ 2 * P.a * P.b * μ P + 4 * P.b * μ P * K
  let C := P.α ^ 2 * P.a ^ 2 * μ P ^ 2 - 4 * P.b * μ P * K * what P
  (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A)

/-- `c^OR` (App. B.2, PDF p. 35). -/
noncomputable def cOR (P : Params) : ℝ :=
  P.a / P.b * P.α * (1 - P.θ) * ((1 - P.α) - Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)))

/-- `c^DA` (App. B.3, PDF p. 36). -/
noncomputable def cDA (P : Params) : ℝ :=
  P.a * P.α * (μ P - P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ))

/-- `c^DR_1` (App. B.4, PDF p. 37). -/
noncomputable def cDR1 (P : Params) : ℝ :=
  P.a * P.α * (1 - P.θ) *
      (μ P ^ 2 + P.θ - 2 * P.θ * Real.sqrt (P.α * μ P * (1 - P.α) * (1 - P.θ))) /
    (P.b * (P.α ^ 2 * (1 - P.θ) ^ 3 + 4 * P.α * P.θ * (1 - P.θ) + P.θ * (1 + P.θ) ^ 2))

/-- `c^DR_2` (App. B.4, PDF p. 37). -/
noncomputable def cDR2 (P : Params) : ℝ :=
  P.a * P.α * μ P * (1 - P.θ) / (P.b * (μ P + P.θ))

/-- `C̃`, (6) (App. C, PDF p. 37). -/
noncomputable def Ctil (P : Params) : ℝ :=
  P.a * P.α * (1 - Real.sqrt (P.α ^ 2 * (1 - P.θ) + P.θ)) / (P.b * (1 + P.α))

/-- `C̄`, (8) (App. C, PDF p. 38). -/
noncomputable def Cbar (P : Params) : ℝ :=
  let φa := P.α * (1 - P.θ) * (P.α - P.α ^ 2 * (1 - P.θ) + 2 * P.θ * (1 - P.α)) + P.θ ^ 2
  let φb := φa + P.α * P.θ * (P.α + μ P * (1 - P.α))
  let φc := P.α * (1 - P.θ) * (2 - P.α) + P.θ
  P.a * P.α / P.b * ((φa - P.θ * μ P * Real.sqrt φc) / φb)

/-- `Θ(α)` (App. C, proof of Proposition 5, PDF p. 39). -/
noncomputable def Theta (α : ℝ) : ℝ :=
  α * (3 * (1 - α - 4 * α ^ 2) + 4 * Real.sqrt (α * (3 + 5 * α + α ^ 2))) /
    ((1 - α) * (3 + 4 * α) ^ 2)

/-- `θ₁(α)` (App. B.1, PDF p. 34). -/
noncomputable def theta1 (α : ℝ) : ℝ :=
  (1 - 4 * α + Real.sqrt (1 + 8 * α)) / (8 * (1 - α))

/-- `θ₂(α)`: the largest real root of `−α³ + α²(5+α)x + (16 − 19α − 6α²)x² − 25(1−α)x³`
("the third root", App. B.1, PDF p. 34). -/
noncomputable def theta2 (α : ℝ) : ℝ :=
  sSup {x : ℝ | -α ^ 3 + α ^ 2 * (5 + α) * x + (16 - 19 * α - 6 * α ^ 2) * x ^ 2
    - 25 * (1 - α) * x ^ 3 = 0}

/-- The regions `H₁, H₂, H₃` of the `(α, θ)` square (App. B.1, PDF p. 34). -/
def H1 (α θ : ℝ) : Prop := 0 < θ ∧ θ < theta1 α

def H2 (α θ : ℝ) : Prop := theta1 α < θ ∧ θ < theta2 α

def H3 (α θ : ℝ) : Prop := theta2 α < θ ∧ θ < 1

end YieldPostpone.Pricing


