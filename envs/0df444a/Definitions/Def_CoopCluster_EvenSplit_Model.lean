-- Prove2me | Definitions.Def_CoopCluster_EvenSplit_Model
-- name    : CoopCluster_EvenSplit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:26.688138+00:00
-- url     : https://prove2.me/theorems/c0b7f371-d44f-4043-a88d-264b9e6fa5bc
-- title:
--   §2–§4, pp. 109–113 — waiting-area entertainment: monopoly profit, co-opetition demands, cost share, joint entertainment stage, symmetric equilibrium
-- statement:
--   This file sets up the service-cluster model of Yuan, Dai, Chen and Gavirneni (2021), for a single service provider (the **local monopolist**) and for two symmetric providers that share waiting-area entertainment (**co-opetition**).
--
--   **Parameters.** $B>0$ is the maximum demand rate, $\beta_0>0$ the customers' price sensitivity, $h>0$ the waiting cost per unit time, $w>0$ the announced waiting-time standard, $\delta>0$ the effectiveness of entertainment, $c>0$ the entertainment cost coefficient and $\gamma\ge 0$ the marginal cost of capacity. The **standing assumptions** are these sign conditions together with
--   $$2\beta_0 c-\delta^2(B-\beta_0\gamma)^2\ge 0,\qquad \beta_0\gamma<B-hw .$$
--
--   **Monopoly (§2).** With service fee $p$ and entertainment level $\alpha$, the arrival rate is
--   $$\lambda(p,\alpha;w)=B-hw\,e^{-\delta\alpha}-\beta_0 p ,$$
--   the entertainment cost is $C(\alpha)=\tfrac12 c\alpha^2$, the service rate needed to keep the expected wait at $w$ is $\mu=\lambda+1/w$, and the profit is
--   $$\Pi(p,\alpha)=p\,\lambda(p,\alpha;w)-C(\alpha)-\gamma\mu .$$
--   A monopoly optimum is a pair $(p,\alpha)$ with $p\ge\gamma$, $\alpha\ge 0$ maximizing $\Pi$ over all such pairs; the set of attainable monopoly profits is $\{\Pi(p,\alpha):p\ge\gamma,\ \alpha\ge 0\}$.
--
--   **Co-opetition (§3 notation, §4).** Write $A=B-\beta_0\gamma$, $D(\alpha)=A-hw\,e^{-\delta\alpha}$, $\beta=\beta_0+\theta$ with price-competition intensity $\theta$, and margins $P_i=p_i-\gamma$. Provider $i$'s arrival rate against rival $j$ is
--   $$\lambda_i=D(\alpha)-\beta P_i+\theta P_j ,$$
--   its cost share with cost-sharing factor $t$ is $\phi(\lambda_i,\lambda_j)=\tfrac12+t(\lambda_i-\lambda_j)$, and its profit is
--   $$\Pi_i=\pi(\alpha,P_i,P_j)=P_i\lambda_i-\phi(\lambda_i,\lambda_j)\,C(\alpha)-\gamma/w .$$
--   In the two-stage game, providers first set margins, then jointly choose $\alpha\ge 0$ to maximize $\Pi_1+\Pi_2$. A **symmetric equilibrium** is a pair $(P,\alpha)$ with $P\ge 0$, $\alpha$ maximizing the joint profit at margins $(P,P)$, and such that for every deviation $P'\ge 0$ and every joint optimum $\alpha'$ at margins $(P',P)$, provider 1's profit $\pi(\alpha',P',P)$ does not exceed $\pi(\alpha,P,P)$. The utilization of a provider with arrival rate $\lambda$ is $\rho=\lambda/\mu$.
--
--   These objects are shared by every statement of the mission: the monopoly benchmark, the equilibrium characterization of Proposition 3 and the comparison of Proposition 7.
--
--   **Formalization Note.** Everything is real-valued. Prices are encoded by margins $P=p-\gamma\ge 0$ (the paper's domain $p\ge\gamma$), both for the equilibrium price and for every deviation. The page's capacity assumption $\gamma\le(B-hw)/\beta_0$ is strengthened to the strict $\beta_0\gamma<B-hw$; at equality the degenerate profile $(P,\alpha)=(0,0)$ can be an equilibrium with co-opetition and monopoly profits both equal to $-\gamma/w$, which falsifies the strict part of Proposition 7(ii). The page prints the demand as $D(\alpha)-\beta P_i+\theta(P_j-P_i)$, which double-counts $\theta$ given $\beta=\beta_0+\theta$; the form $D(\alpha)-\beta P_i+\theta P_j$ of §3 and of Proposition 3(ii) is used. The page's cost-share display gives two inconsistent expressions; the first, $\tfrac12+t(\lambda_i-\lambda_j)$, is used (it agrees with Proposition 3); both coincide at $t=0$, the only case used by the theorems of this mission.
-- source:
--   Yuan, Dai, Chen & Gavirneni, Co-opetition in service clusters with waiting-area entertainment, MSOM 23(1):106–122 (2021), pp. 109–113 (PDF 4–8), §2 eq. (1) and the profit display, §3 notation, §4 demand, cost share and profit displays

import Mathlib

noncomputable section

namespace CoopCluster.EvenSplit

/-- Parameters of the service-cluster model (Yuan, Dai, Chen & Gavirneni 2021, §2):
maximum demand rate `B`, price sensitivity `b0` (β₀), waiting cost `h`, waiting-time standard `w`,
entertainment effectiveness `δ`, entertainment cost coefficient `c`, marginal capacity cost `γ`. -/
structure Params where
  B : ℝ
  b0 : ℝ
  h : ℝ
  w : ℝ
  δ : ℝ
  c : ℝ
  γ : ℝ

/-- Standing assumptions of §2 (pp. 109–110). The last clause strengthens the page's
`γ ≤ (B − hw)/β₀` to the strict `β₀γ < B − hw` (disclosed; needed for the strict clause of
Proposition 7(ii)). -/
def Params.Standing (M : Params) : Prop :=
  0 < M.B ∧ 0 < M.b0 ∧ 0 < M.h ∧ 0 < M.w ∧ 0 < M.δ ∧ 0 < M.c ∧ 0 ≤ M.γ ∧
  0 ≤ 2 * M.b0 * M.c - M.δ ^ 2 * (M.B - M.b0 * M.γ) ^ 2 ∧
  M.b0 * M.γ < M.B - M.h * M.w

/-- Entertainment cost `C(α) = c α² / 2`. -/
def entCost (M : Params) (α : ℝ) : ℝ := M.c * α ^ 2 / 2

/-- Monopoly arrival rate, eq. (1): `λ(p, α; w) = B − h w e^{−δα} − β₀ p`. -/
def monoArrival (M : Params) (p α : ℝ) : ℝ :=
  M.B - M.h * M.w * Real.exp (-(M.δ * α)) - M.b0 * p

/-- Volume-based capacity `µ = λ + 1/w`. -/
def serviceRate (M : Params) (lam : ℝ) : ℝ := lam + 1 / M.w

/-- Monopoly profit `Π = p λ − C(α) − γ µ` (§2, p. 110). -/
def monoProfit (M : Params) (p α : ℝ) : ℝ :=
  p * monoArrival M p α - entCost M α - M.γ * serviceRate M (monoArrival M p α)

/-- The set of attainable monopoly profits over fees `p ≥ γ` and entertainment levels `α ≥ 0`. -/
def monoProfits (M : Params) : Set ℝ :=
  {π | ∃ p α : ℝ, M.γ ≤ p ∧ 0 ≤ α ∧ π = monoProfit M p α}

/-- `(p, α)` is an optimal monopoly decision over `p ≥ γ`, `α ≥ 0`. -/
def IsMonoOpt (M : Params) (p α : ℝ) : Prop :=
  M.γ ≤ p ∧ 0 ≤ α ∧
    ∀ p' α' : ℝ, M.γ ≤ p' → 0 ≤ α' → monoProfit M p' α' ≤ monoProfit M p α

/-- `A = B − β₀ γ` (§3, p. 112). -/
def A (M : Params) : ℝ := M.B - M.b0 * M.γ

/-- `D(α) = A − h w e^{−δα}` (§3, p. 112). -/
def D (M : Params) (α : ℝ) : ℝ := A M - M.h * M.w * Real.exp (-(M.δ * α))

/-- Co-opetition arrival rate of a provider with margin `Pi = pi − γ` against a rival with margin
`Pj`: `λi = D(α) − β Pi + θ Pj` with `β = β₀ + θ`. -/
def arrival (M : Params) (θ α Pi Pj : ℝ) : ℝ := D M α - (M.b0 + θ) * Pi + θ * Pj

/-- Linear cost share `φ(λi, λj) = 1/2 + t (λi − λj)` (§4, p. 113, first form of the display). -/
def costShare (t li lj : ℝ) : ℝ := 1 / 2 + t * (li - lj)

/-- Provider profit `Πi = Pi λi − φ(λi, λj) C(α) − γ/w` (§4, p. 113). -/
def firmProfit (M : Params) (θ t α Pi Pj : ℝ) : ℝ :=
  Pi * arrival M θ α Pi Pj
    - costShare t (arrival M θ α Pi Pj) (arrival M θ α Pj Pi) * entCost M α - M.γ / M.w

/-- Joint profit `Π₁ + Π₂` at margins `(P1, P2)`. -/
def jointProfit (M : Params) (θ t α P1 P2 : ℝ) : ℝ :=
  firmProfit M θ t α P1 P2 + firmProfit M θ t α P2 P1

/-- Second stage: `α ≥ 0` maximizes the joint profit over `α ≥ 0` at margins `(P1, P2)`. -/
def IsJointOpt (M : Params) (θ t P1 P2 α : ℝ) : Prop :=
  0 ≤ α ∧ ∀ α' : ℝ, 0 ≤ α' → jointProfit M θ t α' P1 P2 ≤ jointProfit M θ t α P1 P2

/-- Symmetric equilibrium `(P, α)` of the two-stage co-opetition game: both providers charge
margin `P ≥ 0`, `α` is a joint optimum at `(P, P)`, and no unilateral deviation `P' ≥ 0`, followed
by any joint optimum `α'` at `(P', P)`, raises provider 1's profit. -/
def IsSymEq (M : Params) (θ t P α : ℝ) : Prop :=
  0 ≤ P ∧ IsJointOpt M θ t P P α ∧
    ∀ P' α' : ℝ, 0 ≤ P' → IsJointOpt M θ t P' P α' →
      firmProfit M θ t α' P' P ≤ firmProfit M θ t α P P

/-- Utilization `ρ = λ / µ` (§3, p. 112). -/
def utilization (M : Params) (lam : ℝ) : ℝ := lam / serviceRate M lam

end CoopCluster.EvenSplit

end


