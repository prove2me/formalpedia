-- Prove2me | Definitions.Def_YieldPostpone_Interplay_Setting
-- name    : YieldPostpone_Interplay_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:23:49.082781+00:00
-- url     : https://prove2.me/theorems/89ae195e-33cd-4f62-a0c0-d9c23493575a
-- title:
--   §3, pp. 7–10; App. B (3), PDF p. 33 — two-point yield, linear demand, the four Stackelberg games, subgame-perfect equilibrium, outcome (π_R, π_S, CS), thresholds
-- statement:
--   The model of Geng, Guo, Xiao and Yang: one supplier, one retailer, a deterministic linear market and a random proportional production yield.
--
--   **Parameters.** A demand intercept $a>0$ and slope $b>0$ give demand $d(p)=a-bp$ and inverse demand $p(t)=(a-t)/b$. The yield factor $Y$ takes the value $1$ with probability $\theta$ and $\alpha$ with probability $1-\theta$, with $0<\alpha<1$ and $0<\theta<1$ (display (1)); its mean is $\mu=\alpha(1-\theta)+\theta$. For a function $f$, $\mathbb E f(Y)=\theta f(1)+(1-\theta)f(\alpha)$. The unit production cost $c$ is paid on the whole planned production and is kept as a separate argument, with $0<c<a\mu/b$ (display (3)).
--
--   **Scenarios.** OA, OR, DA, DR: payment is by **order** (O) or by **delivery** (D), and the retail price is set **ex ante** (A, before the yield) or **responsively** (R, after seeing the delivered quantity).
--
--   **Moves.** The supplier posts a wholesale price $w$; the retailer orders $q\ge0$ (and, ex ante, commits to a price $p$); the supplier produces $Q$; the yield $Y$ realizes and $\hat q=\min\{YQ,q\}$ is delivered; under responsive pricing the retailer then sets $p$. The retailer earns $p\min\{d(p),\hat q\}$ minus the transfer $T^k$, which is $wq$ under pay-by-order and $w\min\{YQ,q\}$ under pay-by-delivery; the supplier earns $\mathbb E[T^k]-cQ$. Admissible actions (3): $0<p<a/b$; $c<w<a/b$ under pay-by-order and $c/\mu<w<a/b$ under pay-by-delivery; $Q\ge 0$; under pay-by-order $Q=q$ ("the supplier's production level $Q$ will be exactly the same as the ordered quantity $q$", p. 7).
--
--   **Equilibrium.** A strategy profile $\sigma$ lists the supplier's price $w$, its production rule $Q(w,q)$, the retailer's order rule $q(w)$, its committed price rule $p(w)$ and its ex post price rule $p^{\mathrm{r}}(w,q,x)$. It is a **subgame-perfect equilibrium** of scenario $k$ at cost $c$ when every rule is optimal at every node, on or off the path:
--
--   1. under pay-by-delivery, for every admissible $w$ and every $q\ge0$, $Q(w,q)\ge0$ maximizes $\mathbb E[T^k]-cQ'$ over $Q'\ge0$, and $Q(w,q)=q$ whenever $q$ is itself a maximizer; under pay-by-order $Q(w,q)=q$;
--   2. under responsive pricing, for every $w,q$ and every available quantity $x\ge0$, $p^{\mathrm r}(w,q,x)$ is admissible and maximizes $p\min\{d(p),x\}$ over admissible $p$;
--   3. for every admissible $w$, the order $q(w)\ge 0$ (with an admissible committed price $p(w)$, ex ante) maximizes the retailer's expected profit over all orders $q'\ge0$ (and admissible prices $p'$, ex ante), the later moves following $\sigma$;
--   4. $w$ is admissible and maximizes the supplier's expected profit over admissible $w'$, the later moves following $\sigma$.
--
--   **Outcome.** $\pi^k_R$ and $\pi^k_S$ are the retailer's and supplier's expected profits on the path of $\sigma$, and $CS^k=\mathbb E\,\mathcal S(p,\hat q)$ with
--   $$\mathcal S(p,X)=\int_0^{\min\{d(p),X\}}\big(p(t)-p\big)\,dt,$$
--   where $p$ is the ex post price for OR and DR and the committed price for OA and DA.
--
--   **Thresholds** (Appendices B and C), functions of $(a,b,\alpha,\theta)$ only:
--
--   - $c^{OA}_1=\dfrac{a\alpha(\mu-\alpha\theta-2\theta\sqrt\mu)}{b(\alpha+\theta)}$ and $\hat w=c^{DA}=\dfrac{a\alpha(\mu-\theta\sqrt\mu)}{b(\alpha+\theta)}$;
--   - $c^{OA}_2$, the larger root in $c$ of $\alpha^2(a\mu-bc)^2=4b\mu(a\alpha-b\hat w)(\hat w-c)$;
--   - $c^{OR}=\dfrac ab\alpha(1-\theta)\Big((1-\alpha)-\sqrt{\alpha^2+\tfrac{\theta}{1-\theta}}\Big)$;
--   - $c^{DR}_1=\dfrac{a\alpha(1-\theta)\big(\mu^2+\theta-2\theta\sqrt{\alpha\mu(1-\alpha)(1-\theta)}\big)}{b\big(\alpha^2(1-\theta)^3+4\alpha\theta(1-\theta)+\theta(1+\theta)^2\big)}$ and $c^{DR}_2=\dfrac{a\alpha\mu(1-\theta)}{b(\mu+\theta)}$;
--   - $\tilde C$ of (6), $\bar C$ of (8) and $\Theta(\alpha)$ of PDF p. 39;
--   - $\theta_1(\alpha)=\dfrac{1-4\alpha+\sqrt{1+8\alpha}}{8(1-\alpha)}$, and $\theta_2(\alpha)$, the largest real root of $-\alpha^3+\alpha^2(5+\alpha)x+(16-19\alpha-6\alpha^2)x^2-25(1-\alpha)x^3$;
--   - the regions $\mathcal H_1=\{0<\theta<\theta_1\}$, $\mathcal H_2=\{\theta_1<\theta<\theta_2\}$, $\mathcal H_3=\{\theta_2<\theta<1\}$.
--
--   These objects are shared by every statement of the mission: the equilibrium lemmas, the threshold claims and Proposition 3.
--
--   **Formalization Note** (1) Ties in production: at $w=c/(\alpha(1-\theta))$ the supplier is indifferent among all $Q\in[q,q/\alpha]$. Display (4) assigns that tie to inflation, under which the DR game has no equilibrium for intermediate costs; the equilibrium predicate instead requires $Q=q$ whenever $q$ is optimal, which reproduces Lemma 4's profits. (2) Display (2) prints the scenario labels of the two consumer-surplus formulas swapped; the definition uses the ex post price for the responsive scenarios, as Appendix B does. (3) $c^{OA}_2$ is called "the second root of the polynomial" (a quartic) on PDF p. 34; the quartic is the product of the quadratic above and its conjugate under $\sqrt\mu\mapsto-\sqrt\mu$, and its second root is the quadratic's larger root (checked numerically). The quadratic's discriminant is positive (for $a=b=1$ it equals $16\alpha^2\mu^{3/2}\theta^2(\alpha+\sqrt\mu)(\mu-\alpha^2)/(\alpha+\theta)^2$), so both roots are real. (4) $\theta_2$ is the supremum of the cubic's real root set, which is finite (leading coefficient $-25(1-\alpha)\neq0$) and nonempty (odd degree) for $0<\alpha<1$, so the supremum is the largest root, as "the third root" intends. (5) The regions are stated for $0<\alpha<1$, the model's range, where the page writes $0\le\alpha\le1$. Every square-root argument is nonnegative under the standing ranges.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), pp. 7–10, (1)–(2), Table 1; App. B, PDF pp. 33–34 (appendix pp. 1–2), (3)–(5); App. B–C, PDF pp. 34–39 (appendix pp. 2–7), thresholds c^OA_1, ŵ, c^OA_2, c^OR, c^DA, c^DR_1, c^DR_2, (6), (8), Θ(α), θ₁, θ₂, H₁–H₃

import Mathlib

namespace YieldPostpone.Interplay

/-- The model's parameters (§3.1, p. 7; Table 2, PDF p. 33): demand intercept `a`, demand slope
`b` (demand `d(p) = a - b p`), yield-loss level `α` and probability `θ` of full yield.
The production cost `c` is not a field: every result quantifies over it separately. -/
structure Params where
  a : ℝ
  b : ℝ
  α : ℝ
  θ : ℝ

/-- Standing parameter ranges (1) and Table 2: `a, b > 0`, `0 < α < 1`, `0 < θ < 1`. -/
def Params.Valid (P : Params) : Prop :=
  0 < P.a ∧ 0 < P.b ∧ 0 < P.α ∧ P.α < 1 ∧ 0 < P.θ ∧ P.θ < 1

/-- Expected yield factor `μ = α (1 - θ) + θ` (p. 7). -/
def μ (P : Params) : ℝ := P.α * (1 - P.θ) + P.θ

/-- Expectation over the two-point yield (1): `Y = 1` with probability `θ`, `Y = α` with
probability `1 - θ`. `E P f = 𝔼[f(Y)]`. -/
def E (P : Params) (f : ℝ → ℝ) : ℝ := P.θ * f 1 + (1 - P.θ) * f P.α

/-- Linear demand `d(p) = a - b p`. -/
def demand (P : Params) (p : ℝ) : ℝ := P.a - P.b * p

/-- The four scenarios (§3.3, p. 8): pay-by-Order / pay-by-Delivery, ex Ante / Responsive pricing. -/
inductive Scenario
  | OA
  | OR
  | DA
  | DR
  deriving DecidableEq

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

/-- Delivered quantity `q̂ = min {y Q, q}` at yield realization `y`, production `Q`, order `q`. -/
def delivered (y Q q : ℝ) : ℝ := min (y * Q) q

/-- Transfer payment `T^k` at yield `y` (p. 9): `w min {y Q, q}` under pay-by-delivery,
`w q` under pay-by-order. -/
def transfer (_P : Params) (k : Scenario) (w Q q y : ℝ) : ℝ :=
  if k.byDelivery then w * min (y * Q) q else w * q

/-- Supplier's expected profit at the production stage (p. 9): `𝔼[T^k] - c Q`. -/
def supplierProfit (P : Params) (c : ℝ) (k : Scenario) (w Q q : ℝ) : ℝ :=
  E P (transfer P k w Q q) - c * Q

/-- Admissible wholesale prices (3), PDF p. 33: `c < w < a/b` under pay-by-order and
`c/μ < w < a/b` under pay-by-delivery. -/
def wAdm (P : Params) (c : ℝ) (k : Scenario) (w : ℝ) : Prop :=
  (if k.byDelivery then c / μ P < w else c < w) ∧ w < P.a / P.b

/-- Admissible retail prices (3): `0 < p < a/b`. -/
def pAdm (P : Params) (p : ℝ) : Prop := 0 < p ∧ p < P.a / P.b

/-- Sales revenue `p min {d(p), x}` when `x` units are available for sale (p. 9). -/
def salesRev (P : Params) (p x : ℝ) : ℝ := p * min (demand P p) x

/-- A strategy profile, common to the four scenarios (fields unused in a scenario are ignored).
Each later move is a function of everything observed before it. -/
structure Profile where
  /-- supplier's wholesale price -/
  w : ℝ
  /-- supplier's production level as a function of `(w, q)` -/
  Q : ℝ → ℝ → ℝ
  /-- retailer's order as a function of `w` -/
  q : ℝ → ℝ
  /-- retailer's committed (ex ante) retail price as a function of `w` (OA, DA) -/
  p : ℝ → ℝ
  /-- retailer's ex post retail price as a function of `(w, q, delivered quantity)` (OR, DR) -/
  pr : ℝ → ℝ → ℝ → ℝ

/-- Retailer's expected profit (p. 9) at wholesale price `w` when it orders `q'` and (ex ante)
commits to price `p'`, with the production and ex post pricing given by `σ`. -/
def retailerProfit (P : Params) (k : Scenario) (σ : Profile) (w q' p' : ℝ) : ℝ :=
  E P (fun y =>
    let x := delivered y (σ.Q w q') q'
    (if k.responsive then salesRev P (σ.pr w q' x) x else salesRev P p' x) -
      transfer P k w (σ.Q w q') q' y)

/-- Supplier's expected profit when it posts `w'` and play continues according to `σ`. -/
def supplierValue (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) (w' : ℝ) : ℝ :=
  supplierProfit P c k w' (σ.Q w' (σ.q w')) (σ.q w')

/-- `σ` is a subgame-perfect equilibrium of the Stackelberg game of scenario `k` at cost `c`
(Table 1, p. 9; §4, p. 10). Optimality is required at every decision node:
1. production: under pay-by-delivery, for every admissible `w` and order `q ≥ 0`, `σ.Q w q ≥ 0`
   maximizes the supplier's expected profit over `Q' ≥ 0`, and equals `q` whenever `Q' = q` is
   itself a maximizer (series tie rule); under pay-by-order `σ.Q w q = q` (p. 7);
2. ex post price (responsive scenarios): for every `w`, `q`, and delivered quantity `x ≥ 0`, the
   price is admissible and maximizes `p min {d(p), x}` over admissible prices;
3. retailer: for every admissible `w`, the order is `≥ 0`, the committed price is admissible (ex
   ante), and the pair maximizes the retailer's expected profit over orders `q' ≥ 0` (and
   admissible prices `p'`, ex ante);
4. supplier: `σ.w` is admissible and maximizes the supplier's expected profit over admissible `w'`. -/
def IsSPE (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) : Prop :=
  (∀ w q : ℝ, wAdm P c k w → 0 ≤ q →
      (k.byDelivery = true →
        0 ≤ σ.Q w q ∧
        (∀ Q' : ℝ, 0 ≤ Q' → supplierProfit P c k w Q' q ≤ supplierProfit P c k w (σ.Q w q) q) ∧
        ((∀ Q' : ℝ, 0 ≤ Q' → supplierProfit P c k w Q' q ≤ supplierProfit P c k w q q) →
          σ.Q w q = q)) ∧
      (k.byDelivery = false → σ.Q w q = q)) ∧
  (k.responsive = true → ∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧ ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x) ∧
  (∀ w : ℝ, wAdm P c k w →
      0 ≤ σ.q w ∧ (k.responsive = false → pAdm P (σ.p w)) ∧
      ∀ q' p' : ℝ, 0 ≤ q' → (k.responsive = false → pAdm P p') →
        retailerProfit P k σ w q' p' ≤ retailerProfit P k σ w (σ.q w) (σ.p w)) ∧
  (wAdm P c k σ.w ∧ ∀ w' : ℝ, wAdm P c k w' → supplierValue P c k σ w' ≤ supplierValue P c k σ σ.w)

/-- Consumer surplus `𝒮(p, X) = ∫₀^{min {d(p), X}} (p(t) - p) dt` with inverse demand
`p(t) = (a - t)/b` (p. 10). -/
noncomputable def surplus (P : Params) (p X : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(min (demand P p) X), ((P.a - t) / P.b - p)

/-- Retailer's equilibrium-path expected profit `π^k_R`. -/
def piR (P : Params) (_c : ℝ) (k : Scenario) (σ : Profile) : ℝ :=
  retailerProfit P k σ σ.w (σ.q σ.w) (σ.p σ.w)

/-- Supplier's equilibrium-path expected profit `π^k_S`. -/
def piS (P : Params) (c : ℝ) (k : Scenario) (σ : Profile) : ℝ :=
  supplierValue P c k σ σ.w

/-- Expected consumer surplus `CS^k` on the path of `σ` (p. 10, (2) with the scenario labels as
used in App. B): the ex post price for OR/DR, the committed price for OA/DA. -/
noncomputable def CS (P : Params) (_c : ℝ) (k : Scenario) (σ : Profile) : ℝ :=
  E P (fun y =>
    let w := σ.w
    let q := σ.q w
    let x := delivered y (σ.Q w q) q
    surplus P (if k.responsive then σ.pr w q x else σ.p w) x)

/-! ### Thresholds (App. B–C), functions of the parameters only -/

/-- `c^OA_1 = a α (μ - α θ - 2 θ √μ) / (b (α + θ))` (App. B.1, PDF p. 34). -/
noncomputable def cOA1 (P : Params) : ℝ :=
  P.a * P.α * (μ P - P.α * P.θ - 2 * P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ))

/-- `ŵ = a α (μ - θ √μ) / (b (α + θ))` (App. B.1, PDF pp. 34–35). -/
noncomputable def what (P : Params) : ℝ :=
  P.a * P.α * (μ P - P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ))

/-- `c^OA_2`: the larger root in `c` of `α² (a μ - b c)² = 4 b μ (a α - b ŵ)(ŵ - c)`, written by
the quadratic formula (series convention for "the second root of the polynomial", PDF p. 34). -/
noncomputable def cOA2 (P : Params) : ℝ :=
  let K := 4 * P.b * μ P * (P.a * P.α - P.b * what P)
  let A := P.α ^ 2 * P.b ^ 2
  let B := -2 * P.α ^ 2 * P.a * P.b * μ P + K
  let C := P.α ^ 2 * P.a ^ 2 * μ P ^ 2 - K * what P
  (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A)

/-- `c^OR = (a/b) α (1 - θ) ((1 - α) - √(α² + θ/(1 - θ)))` (App. B.2, PDF p. 35). -/
noncomputable def cOR (P : Params) : ℝ :=
  P.a / P.b * P.α * (1 - P.θ) * ((1 - P.α) - Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)))

/-- `c^DA = a α (μ - θ √μ) / (b (α + θ))` (App. B.3, PDF p. 36). -/
noncomputable def cDA (P : Params) : ℝ :=
  P.a * P.α * (μ P - P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ))

/-- `c^DR_1` (App. B.4, PDF p. 37). -/
noncomputable def cDR1 (P : Params) : ℝ :=
  P.a * P.α * (1 - P.θ) *
      (μ P ^ 2 + P.θ - 2 * P.θ * Real.sqrt (P.α * μ P * (1 - P.α) * (1 - P.θ))) /
    (P.b * (P.α ^ 2 * (1 - P.θ) ^ 3 + 4 * P.α * P.θ * (1 - P.θ) + P.θ * (1 + P.θ) ^ 2))

/-- `c^DR_2 = a α μ (1 - θ) / (b (μ + θ))` (App. B.4, PDF p. 37). -/
noncomputable def cDR2 (P : Params) : ℝ :=
  P.a * P.α * μ P * (1 - P.θ) / (P.b * (μ P + P.θ))

/-- `C̃ = a α (1 - √(α² (1 - θ) + θ)) / (b (1 + α))`, (6), PDF p. 37. -/
noncomputable def Ctil (P : Params) : ℝ :=
  P.a * P.α * (1 - Real.sqrt (P.α ^ 2 * (1 - P.θ) + P.θ)) / (P.b * (1 + P.α))

/-- `C̄ = (a α / b)(φ_a - θ μ √φ_c)/φ_b`, (8), PDF p. 38. -/
noncomputable def Cbar (P : Params) : ℝ :=
  let φa := P.α * (1 - P.θ) * (P.α - P.α ^ 2 * (1 - P.θ) + 2 * P.θ * (1 - P.α)) + P.θ ^ 2
  let φb := φa + P.α * P.θ * (P.α + μ P * (1 - P.α))
  let φc := P.α * (1 - P.θ) * (2 - P.α) + P.θ
  P.a * P.α / P.b * ((φa - P.θ * μ P * Real.sqrt φc) / φb)

/-- `Θ(α) = α (3 (1 - α - 4 α²) + 4 √(α (3 + 5 α + α²))) / ((1 - α)(3 + 4 α)²)` (PDF p. 39). -/
noncomputable def Theta (α : ℝ) : ℝ :=
  α * (3 * (1 - α - 4 * α ^ 2) + 4 * Real.sqrt (α * (3 + 5 * α + α ^ 2))) /
    ((1 - α) * (3 + 4 * α) ^ 2)

/-- `θ₁(α) = (1 - 4 α + √(1 + 8 α)) / (8 (1 - α))` (PDF p. 34). -/
noncomputable def theta1 (α : ℝ) : ℝ :=
  (1 - 4 * α + Real.sqrt (1 + 8 * α)) / (8 * (1 - α))

/-- `θ₂(α)`: the largest real root of `-α³ + α² (5 + α) x + (16 - 19 α - 6 α²) x² - 25 (1 - α) x³`
(PDF p. 34, "the third root"). -/
noncomputable def theta2 (α : ℝ) : ℝ :=
  sSup {x : ℝ | -α ^ 3 + α ^ 2 * (5 + α) * x + (16 - 19 * α - 6 * α ^ 2) * x ^ 2
      - 25 * (1 - α) * x ^ 3 = 0}

/-- Region `H₁ = {0 < θ < θ₁(α)}` (PDF p. 34). -/
def H1 (α θ : ℝ) : Prop := 0 < θ ∧ θ < theta1 α

/-- Region `H₂ = {θ₁(α) < θ < θ₂(α)}` (PDF p. 34). -/
def H2 (α θ : ℝ) : Prop := theta1 α < θ ∧ θ < theta2 α

/-- Region `H₃ = {θ₂(α) < θ < 1}` (PDF p. 34). -/
def H3 (α θ : ℝ) : Prop := theta2 α < θ ∧ θ < 1

end YieldPostpone.Interplay


