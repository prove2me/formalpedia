-- Prove2me | Definitions.Def_FoodDeliv_Decentral_Model
-- name    : FoodDeliv_Decentral_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:44:29.924009+00:00
-- url     : https://prove2.me/theorems/c430d0a5-a712-4ac0-95c0-7d4de0d095be
-- title:
--   The base model and decentralized game: utilities (C.1)–(C.2), customer equilibrium, platform best response, restaurant optimum, SPE outcome, thresholds χ, λ1, λ2, ϕ1 (§§3–4, pp. 5–8; OA pp. 7, 19–23)
-- statement:
--   The decentralized food-delivery game of Chen, Hu and Wang (§3, pp. 5–7; §4, p. 8; Online Appendix pp. 7, 19–23).
--
--   **Parameters.** A restaurant's kitchen serves meals at rate $\mu>0$; at total joining rate $\lambda<\mu$ the expected wait for food is $1/(\mu-\lambda)$. A meal is worth $R$ to a customer. Walk-in customers incur waiting cost rate $c>0$; customers using the delivery platform incur $\phi\in[0,c)$. Tech-savvy customers arrive at rate $\Lambda_1$ and may walk in, use food delivery, or balk; traditional customers arrive at rate $\Lambda_0$ and may walk in or balk. The **standing assumptions** are
--   $$\mu>0,\quad c>0,\quad 0\le\phi<c,\quad \Lambda_0\ge\mu,\quad 0<\Lambda_1<\mu,\quad c<R\mu .$$
--
--   **Utilities** (eqs. (C.1)–(C.2)). At food price $p$, delivery fee $\theta$ and total joining rate $\lambda$,
--   $$U_W(\lambda)=R-p-\frac{c}{\mu-\lambda},\qquad U_D(\lambda)=R-p-\theta-\frac{\phi}{\mu-\lambda},$$
--   and balking gives $0$.
--
--   **Customers' equilibrium** (p. 7). A profile $(\lambda_D,\lambda_{1W},\lambda_{0W})$ of delivery and walk-in rates of tech-savvy customers and walk-in rate of traditional customers, with $\lambda_W=\lambda_{0W}+\lambda_{1W}$ and $\lambda=\lambda_D+\lambda_W$, is an equilibrium under $(p,\theta)$ if all rates are nonnegative, $\lambda_D+\lambda_{1W}\le\Lambda_1$, $\lambda_{0W}\le\Lambda_0$, $\lambda<\mu$, and, evaluating utilities at $\lambda$:
--   1. $\lambda_{0W}>0\Rightarrow U_W\ge0$ and $\lambda_{0W}<\Lambda_0\Rightarrow U_W\le 0$;
--   2. $\lambda_D>0\Rightarrow U_D\ge 0$ and $U_D\ge U_W$;
--   3. $\lambda_{1W}>0\Rightarrow U_W\ge0$ and $U_W>U_D$;
--   4. $\lambda_D+\lambda_{1W}<\Lambda_1\Rightarrow U_D\le0$, $U_W\le 0$, and, if $U_D=U_W\ge 0$, then $\lambda_{0W}=0$.
--
--   **The game** (p. 8). The restaurant sets $p\ge0$, then the platform sets $\theta\ge0$, then customers play an equilibrium. With a customers' response $\sigma(p,\theta)$, the platform's profit is $\pi(p,\theta)=\theta\,\lambda_D(\sigma(p,\theta))$; a **best-response fee** to $p$ is a $\theta\ge0$ maximizing $\pi(p,\cdot)$ over $[0,\infty)$. With a fee rule $\theta(\cdot)$ the restaurant's profit is $\Pi(p)=p\,\lambda(\sigma(p,\theta(p)))$; an **optimal price** is a $p\ge0$ maximizing $\Pi$ over $[0,\infty)$. **Social welfare** at price $p$ is
--   $$S=\Pi+\pi+\lambda_D U_D(\lambda)+\lambda_W U_W(\lambda),$$
--   restaurant profit, platform profit and customers' surplus ("the total surpluses from all stakeholders", p. 8). A **subgame-perfect equilibrium** (SPE) is a triple $(\sigma,\theta(\cdot),p^*)$ in which $\sigma(p,\theta)$ is a customers' equilibrium for all $p,\theta\ge0$, $\theta(p)$ is a best-response fee for every $p\ge0$, and $p^*$ is an optimal price. Its **outcome** is $p^*$, $\theta^*=\theta(p^*)$, $\lambda^*_D,\lambda^*_W$ from $\sigma(p^*,\theta^*)$, $\Pi^*=\Pi(p^*)$, $\pi^*=\pi(p^*,\theta^*)$ and $S^*$.
--
--   **Thresholds** (Online Appendix pp. 19–23). $\chi$ is the root of $-R\chi^3-\mu\phi\chi+2\mu^2\phi=0$ in $[0,\mu]$ and $\lambda_2=\mu-\chi$; $\lambda_1$ is the smallest $\lambda\in(0,\mu)$ with $\lambda\big(R-\mu\phi/(\mu-\lambda)^2\big)=(\sqrt{R\mu}-\sqrt c)^2$;
--   $$\chi_1=\frac{3R\mu-(c-2\sqrt{Rc\mu})-\sqrt{(3R\mu-(c-2\sqrt{Rc\mu}))^2+16R\mu(c-2\sqrt{Rc\mu})}}{4R},\qquad \phi_1=\frac{R\chi_1^3}{\mu(2\mu-\chi_1)} .$$
--
--   This model is the common ground of every statement of the mission; the equilibrium is defined by optimality conditions only, never by the paper's tables.
--
--   **Formalization Note** The kitchen is modelled only through the expected wait $1/(\mu-\lambda)$, as the paper uses. $c<R\mu$ is not stated in the paper but used in its proofs ("$R\mu/c>1$", Online Appendix p. 21). The tie-breaking rule of p. 7 ("tech-savvy customers use food delivery services if … $U_D(\lambda)=U_W(\lambda)\ge0$") is encoded by the strictness in condition 3 and by the last clause of condition 4: at such a tie no tech-savvy customer walks in, and none balks while traditional customers walk in. $\chi$ and $\lambda_1$ are infima of their root sets (Lean's `sInf`); $\chi$'s set is nonempty under the standing assumptions, and $\lambda_1$ is used only where its root set is nonempty (otherwise `sInf` returns $0$). Prices are restricted to $p\ge0$ and fees to $\theta\ge0$, as in the game.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), pp. 5–8, §§3–4; OA p. 7, eqs. (C.1)–(C.2); OA pp. 19–23 (χ, λ1, λ2, χ1, ϕ1)

import Mathlib

namespace FoodDeliv.Decentral

/-! Base model and decentralized game of Chen, Hu & Wang, *Food Delivery Service and Restaurant:
Friend or Foe?* (SSRN 3469971), §3 (pp. 5–7), §4 (p. 8) and eqs. (C.1)–(C.2) (Online Appendix p. 7).

A restaurant's kitchen is a single-server queue with service rate `μ`; at total joining rate
`l < μ` the expected wait for food is `1 / (μ - l)`. Customers get reward `R`, pay the food price
`p`, and incur waiting cost rate `c` when walking in, or `ϕ` when using the delivery platform,
which also charges the delivery fee `θ`. Tech-savvy customers arrive at rate `Λ1` and may walk in,
use delivery or balk; traditional customers arrive at rate `Λ0` and may walk in or balk. The
delivery-worker pool is unlimited with zero opportunity cost, so deliveries carry no wage and no
capacity constraint. The game: the restaurant sets `p ≥ 0`, then the platform sets `θ ≥ 0`, then
customers play a symmetric (mixed) equilibrium. -/

/-- The primitive parameters of the model (§3, pp. 5–7). -/
structure Params where
  /-- service reward of a meal -/
  R : ℝ
  /-- service rate of the kitchen -/
  μ : ℝ
  /-- waiting cost rate of walk-in customers -/
  c : ℝ
  /-- waiting cost rate of food-delivery customers -/
  ϕ : ℝ
  /-- arrival rate of traditional customers -/
  Λ0 : ℝ
  /-- arrival rate of tech-savvy customers -/
  Λ1 : ℝ

/-- The standing assumptions: `μ > 0`, `c > 0`, `ϕ ∈ [0, c)` (p. 6), `Λ0 ≥ μ` (p. 6),
`0 < Λ1 < μ` (Online Appendix p. 7: "we focus on the condition of Λ1 < μ"), and `c < R μ`, which
the paper uses in its proofs ("Rμ/c > 1", Online Appendix p. 21) without stating it. -/
structure Params.Standing (P : Params) : Prop where
  μ_pos : 0 < P.μ
  c_pos : 0 < P.c
  c_lt_Rμ : P.c < P.R * P.μ
  ϕ_nonneg : 0 ≤ P.ϕ
  ϕ_lt_c : P.ϕ < P.c
  μ_le_Λ0 : P.μ ≤ P.Λ0
  Λ1_pos : 0 < P.Λ1
  Λ1_lt_μ : P.Λ1 < P.μ

/-- Expected utility of a walk-in customer at food price `p` and total joining rate `l`,
eq. (C.1): `U_W(l) = R - p - c / (μ - l)`. -/
noncomputable def UW (P : Params) (p l : ℝ) : ℝ := P.R - p - P.c / (P.μ - l)

/-- Expected utility of a food-delivery customer at food price `p`, delivery fee `θ` and total
joining rate `l`, eq. (C.2): `U_D(l) = R - p - θ - ϕ / (μ - l)`. -/
noncomputable def UD (P : Params) (p θ l : ℝ) : ℝ := P.R - p - θ - P.ϕ / (P.μ - l)

/-- A customer strategy profile, as joining rates (p. 7): `lamD` and `lam1W` are the rates of
tech-savvy customers who use food delivery and who walk in; `lam0W` is the rate of traditional
customers who walk in. -/
structure Profile where
  lamD : ℝ
  lam1W : ℝ
  lam0W : ℝ

/-- Total walk-in rate `λ_W = λ_{0W} + λ_{1W}`. -/
def Profile.lamW (s : Profile) : ℝ := s.lam0W + s.lam1W

/-- Effective arrival rate to the kitchen `λ = λ_W + λ_D`. -/
def Profile.total (s : Profile) : ℝ := s.lamD + s.lamW

/-- `s` is a customers' equilibrium under food price `p` and delivery fee `θ` (p. 7): rates are
feasible, the queue is stable, every option used by a positive rate is a best reply at the
induced total rate `λ`, and an arrival stream not fully joining is indifferent to balking (or
prefers it). Tie-breaking rule (p. 7): tech-savvy customers use food delivery when
`U_D(λ) = U_W(λ) ≥ 0`. So then no tech-savvy customer walks in, and no tech-savvy customer
balks while traditional customers walk in: at such a tie the tech-savvy customers' delivery
demand is served before traditional walk-ins. -/
structure IsCustEq (P : Params) (p θ : ℝ) (s : Profile) : Prop where
  lamD_nonneg : 0 ≤ s.lamD
  lam1W_nonneg : 0 ≤ s.lam1W
  lam0W_nonneg : 0 ≤ s.lam0W
  tech_le : s.lamD + s.lam1W ≤ P.Λ1
  trad_le : s.lam0W ≤ P.Λ0
  total_lt : s.total < P.μ
  /-- traditional customers who walk in get nonnegative utility -/
  trad_join : 0 < s.lam0W → 0 ≤ UW P p s.total
  /-- traditional customers who balk get nonpositive walk-in utility -/
  trad_balk : s.lam0W < P.Λ0 → UW P p s.total ≤ 0
  /-- delivery is used only if it is a best option (ties with walking in go to delivery) -/
  tech_deliv : 0 < s.lamD → 0 ≤ UD P p θ s.total ∧ UW P p s.total ≤ UD P p θ s.total
  /-- tech-savvy customers walk in only if walking in is strictly better than delivery -/
  tech_walk : 0 < s.lam1W → 0 ≤ UW P p s.total ∧ UD P p θ s.total < UW P p s.total
  /-- tech-savvy customers balk only if neither option is positive; in the tie
  `U_D = U_W ≥ 0` they use delivery, so they balk only when no traditional customer walks in -/
  tech_balk : s.lamD + s.lam1W < P.Λ1 →
    UD P p θ s.total ≤ 0 ∧ UW P p s.total ≤ 0 ∧
      (UD P p θ s.total = UW P p s.total ∧ 0 ≤ UW P p s.total → s.lam0W = 0)

/-- The platform's profit `π(p, θ) = θ λ_D` when customers respond to `(p, θ)` by `σ p θ`. -/
def platProfit (σ : ℝ → ℝ → Profile) (p θ : ℝ) : ℝ := θ * (σ p θ).lamD

/-- `θ` is a best-response delivery fee of the platform to the food price `p`: `θ ≥ 0` and it
maximizes `θ' ↦ θ' λ_D(p, θ')` over all `θ' ≥ 0`. -/
def IsFeeBR (σ : ℝ → ℝ → Profile) (p θ : ℝ) : Prop :=
  0 ≤ θ ∧ ∀ θ' : ℝ, 0 ≤ θ' → platProfit σ p θ' ≤ platProfit σ p θ

/-- The restaurant's profit `Π(p) = p (λ_D + λ_W)` at food price `p` when the platform responds
with the fee `fee p` and customers with `σ p (fee p)`. -/
def restProfit (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ) (p : ℝ) : ℝ :=
  p * (σ p (fee p)).total

/-- `p` is an optimal food price for the restaurant: `p ≥ 0` and it maximizes `Π` over all
prices `p' ≥ 0`. -/
def IsOptPrice (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ) (p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ p' : ℝ, 0 ≤ p' → restProfit σ fee p' ≤ restProfit σ fee p

/-- Social welfare at food price `p` (p. 8, "the total surpluses from all stakeholders"):
restaurant profit, platform profit, and the surplus `λ_D U_D(λ) + λ_W U_W(λ)` of the customers. -/
noncomputable def welfare (P : Params) (σ : ℝ → ℝ → Profile) (fee : ℝ → ℝ) (p : ℝ) : ℝ :=
  restProfit σ fee p + platProfit σ p (fee p)
    + (σ p (fee p)).lamD * UD P p (fee p) (σ p (fee p)).total
    + (σ p (fee p)).lamW * UW P p (σ p (fee p)).total

/-- A strategy profile of the three-stage game: the customers' response `σ p θ` to every
`(p, θ)`, the platform's fee rule `fee p`, and the restaurant's price. -/
structure Strategy where
  σ : ℝ → ℝ → Profile
  fee : ℝ → ℝ
  price : ℝ

/-- `E` is a subgame-perfect equilibrium of the decentralized game (§4, p. 8): customers play an
equilibrium after every `p ≥ 0`, `θ ≥ 0`; the platform best-responds to every `p ≥ 0`; and the
restaurant's price is optimal given both. -/
structure IsSPE (P : Params) (E : Strategy) : Prop where
  cust : ∀ p θ : ℝ, 0 ≤ p → 0 ≤ θ → IsCustEq P p θ (E.σ p θ)
  fee_br : ∀ p : ℝ, 0 ≤ p → IsFeeBR E.σ p (E.fee p)
  price_opt : IsOptPrice E.σ E.fee E.price

/-- Equilibrium food price `p*`. -/
def Strategy.pStar (E : Strategy) : ℝ := E.price

/-- Equilibrium delivery fee `θ* = θ*(p*)`. -/
def Strategy.θStar (E : Strategy) : ℝ := E.fee E.price

/-- Equilibrium joining rate of food-delivery customers `λ*_D`. -/
def Strategy.lamDStar (E : Strategy) : ℝ := (E.σ E.price (E.fee E.price)).lamD

/-- Equilibrium joining rate of walk-in customers `λ*_W`. -/
def Strategy.lamWStar (E : Strategy) : ℝ := (E.σ E.price (E.fee E.price)).lamW

/-- Equilibrium restaurant profit `Π* = p* (λ*_D + λ*_W)`. -/
def Strategy.restProfitStar (E : Strategy) : ℝ := restProfit E.σ E.fee E.price

/-- Equilibrium platform profit `π* = θ* λ*_D`. -/
def Strategy.platProfitStar (E : Strategy) : ℝ := platProfit E.σ E.price (E.fee E.price)

/-- Equilibrium social welfare `S* = Π* + π* + λ*_D U_D(λ*) + λ*_W U_W(λ*)`. -/
noncomputable def Strategy.welfareStar (P : Params) (E : Strategy) : ℝ :=
  welfare P E.σ E.fee E.price

/-! Thresholds of the proof (Online Appendix pp. 19–23). -/

/-- The cubic `-R x³ - μ ϕ x + 2 μ² ϕ` of Lemma C.7 (Online Appendix p. 20). -/
def chiCubic (R μ ϕ x : ℝ) : ℝ := -R * x ^ 3 - μ * ϕ * x + 2 * μ ^ 2 * ϕ

/-- `χ`, "the unique real root of `-Rχ³ - μϕχ + 2μ²ϕ = 0` in `[0, μ]`" (Online Appendix p. 19),
taken as the least root in `[0, μ]`. -/
noncomputable def chi (R μ ϕ : ℝ) : ℝ := sInf {x : ℝ | x ∈ Set.Icc 0 μ ∧ chiCubic R μ ϕ x = 0}

/-- `λ2 ≡ μ - χ` (Lemma C.8(3), Online Appendix p. 22). -/
noncomputable def lam2 (R μ ϕ : ℝ) : ℝ := μ - chi R μ ϕ

/-- The delivery-only profit curve `λ (R - μϕ/(μ - λ)²)` of Lemma C.8(3). -/
noncomputable def deliveryCurve (R μ ϕ l : ℝ) : ℝ := l * (R - μ * ϕ / (μ - l) ^ 2)

/-- `λ1`, "the smallest `λ` satisfying `λ (R - μϕ/(μ - λ)²) = (√(Rμ) - √c)²`" (Online Appendix
p. 23), the root taken in `0 < λ < μ`. -/
noncomputable def lam1 (R μ c ϕ : ℝ) : ℝ :=
  sInf {l : ℝ | l ∈ Set.Ioo 0 μ ∧
    deliveryCurve R μ ϕ l = (Real.sqrt (R * μ) - Real.sqrt c) ^ 2}

/-- `χ1` (Online Appendix p. 23). -/
noncomputable def chi1 (R μ c : ℝ) : ℝ :=
  (3 * R * μ - (c - 2 * Real.sqrt (R * c * μ))
    - Real.sqrt ((3 * R * μ - (c - 2 * Real.sqrt (R * c * μ))) ^ 2
      + 16 * R * μ * (c - 2 * Real.sqrt (R * c * μ)))) / (4 * R)

/-- `ϕ1 = R χ1³ / (μ (2μ - χ1))` (Online Appendix p. 23). -/
noncomputable def phi1 (R μ c : ℝ) : ℝ := R * chi1 R μ c ^ 3 / (μ * (2 * μ - chi1 R μ c))

end FoodDeliv.Decentral


