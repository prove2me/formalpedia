-- Prove2me | Definitions.Def_CompetingChains_Cournot_Setting
-- name    : CompetingChains_Cournot_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:49.019493+00:00
-- url     : https://prove2.me/theorems/ff857b06-245a-46c0-b492-3a2d5fba6637
-- title:
--   §3, §5.1–§5.3, pp. 7–21 — standing assumptions, Cournot response coefficients (Lemma 2(a)), ex-ante profits, value of information, side payment, stage-one game (Table 1)
-- statement:
--   Two identical supply chains $i=1,2$ each consist of one manufacturer and one retailer. Retailer $i$ faces the inverse demand $p_i=a+\theta-q_i-\gamma_C q_j$, where $\theta$ is a demand shock with mean $0$ and variance $\sigma^2$ and $\gamma_C\in(0,1)$ measures competition intensity. Manufacturer $i$ has unit production cost $c$ and can reduce it by $x_i$ at effort cost $\tfrac12 k x_i^2$. Retailer $i$ observes a demand signal $Y_i$ of accuracy $t$ and may share it with manufacturer $i$; the **arrangement** of chain $i$ is $X_i=S$ (share) or $X_i=N$ (not share). Write $\tau=t\sigma^2$.
--
--   The definition records the paper's reduced form of this model.
--
--   1. **Standing assumptions** (§5, p. 13): $0<c<a$, $k>a/(4c)$, $k>1/3$, $0<\gamma_C<1$, $t>0$, $\sigma^2>0$.
--   2. The signal weight $s=\tau/(1+\tau)$, with $E[\theta\mid Y_i]=E[Y_j\mid Y_i]=sY_i$ (p. 8), and the signal term $t\sigma^4/(t\sigma^2+1)$.
--   3. **Response coefficients** (Lemma 2(a), p. 15): retailer $i$'s equilibrium quantity is $q_i^{X_iX_j}=\bar q+C_i^{X_iX_j}Y_i$ with $\bar q=k(a-c)/((\gamma_C+4)k-1)$ and
--   $$
--   \begin{aligned}
--   C^{SS}&=\frac{k\tau}{(4\tau+4+\gamma_C\tau)k-(\tau+1)}, &
--   C^{SN}&=\frac{[2+(2-\gamma_C)\tau]k\tau}{(8(1+\tau)^2-\gamma_C^2\tau^2)k-2(\tau+1)^2},\\
--   C^{NS}&=\frac{[(4+4\tau-\gamma_C\tau)k-(\tau+1)]\tau}{(8(\tau+1)^2-\gamma_C^2\tau^2)k-2(\tau+1)^2}, &
--   C^{NN}&=\frac{\tau}{2(\tau+1)+\gamma_C\tau}.
--   \end{aligned}
--   $$
--   4. Retailer $i$'s **best responses** (7) and (9) (p. 14), as functions of $m=E[\theta\mid Y_i]$, $e=E[q_j\mid Y_i]$ and $E=E[q_j]$: $\hat q^S=\frac{k}{4k-1}(a+m-\gamma_C e-c)$ and $\hat q^N=\frac{k}{4k-1}(a-c)+\frac12\big(m-\gamma_C e+\frac{2k-1}{4k-1}\gamma_C E\big)$.
--   5. **Ex-ante profits** (p. 17), when chain $j$'s quantity responds to $Y_j$ with coefficient $C_j$: with $I=(a-c)^2/(4k+k\gamma_C-1)^2$ and $T=t\sigma^4/(t\sigma^2+1)$,
--   $$
--   \begin{aligned}
--   \pi^S_{R}(C_j)&=k^2I+\tfrac{k^2}{(4k-1)^2}(1-\gamma_CC_j)^2T, & \pi^S_{M}(C_j)&=\tfrac{k(4k-1)}{2}I+\tfrac{k}{2(4k-1)}(1-\gamma_CC_j)^2T,\\
--   \pi^N_{R}(C_j)&=k^2I+\tfrac14(1-\gamma_CC_j)^2T, & \pi^N_{M}(C_j)&=\tfrac{k(4k-1)}{2}I,
--   \end{aligned}
--   $$
--   and the chain's profit $\pi^X=\pi^X_R+\pi^X_M$.
--   6. **Equilibrium profits** $\Pi^{X_iX_j}_{\cdot}=\pi^{X_i}_{\cdot}(C_j^{X_jX_i})$ (p. 17), where the rival's coefficient carries the rival's arrangement first.
--   7. The **value of information sharing** $V^{X_j}=\Pi^{SX_j}-\Pi^{NX_j}$ (p. 18) and manufacturer $i$'s optimal **side payment** (p. 21): $\hat m^{X_j}=\Pi^{NX_j}_R-\Pi^{SX_j}_R$ if $\Pi^{NX_j}_R>\Pi^{SX_j}_R$, and $0$ otherwise.
--   8. The **stage-one game** (§5.3, Table 1): the players are the two manufacturers, manufacturer $i$ chooses $X_i\in\{S,N\}$, and its payoff is
--   $$
--   u(X_i,X_j)=\begin{cases}\Pi^{SX_j}_M-\hat m^{X_j}, & X_i=S,\\ \Pi^{NX_j}_M, & X_i=N.\end{cases}
--   $$
--   Manufacturer 1's payoff at $(X_1,X_2)$ is $u(X_1,X_2)$ and manufacturer 2's is $u(X_2,X_1)$. The **equilibria** are the pure-strategy Nash equilibria of this game.
--
--   These objects are the vocabulary of Propositions 6(a) and 7(a).
--
--   **Formalization Note** The Bayesian stages of the model enter only through the closed forms the paper derives (Lemma 2(a), p. 17); they are definitions, not hypotheses. The printed $\pi_{i,C}$ is not transcribed: the chain profit is defined as the sum $\pi_R+\pi_M$, which agrees with the printed formula. Divisions are real divisions, nonzero under $k>1/3$, $\gamma_C\ge0$, $\tau>0$; every theorem carries these hypotheses. For $k>1/2$ the payoff $u(S,X_j)$ equals Table 1's entry $\Pi^{NX_j}_M+V^{X_j}$; for $k\le1/2$ the side payment is $0$ (p. 20), so the payoff is defined with $\hat m$ rather than copied from Table 1. The standing assumptions add $0<c$, $0<t$, $0<\sigma^2$ (positive by definition in §3) and $0<\gamma_C$ (at $\gamma_C=0$ the chains do not interact and Proposition 6(a)(2) fails).
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), pp. 7–21: §3 (1) p. 7 and the information structure p. 8; §5 standing assumptions p. 13; (7), (9) p. 14; Lemma 2(a) p. 15; ex-ante profits p. 17; V p. 18; side payment p. 21; Table 1 p. 21

import Mathlib
import Definitions.Def_CompetingChains_Cournot_TwoPlayerGame

namespace CompetingChains.Cournot

/-- Information sharing arrangement of a supply chain (§5, p. 13): `S` = the retailer shares its
demand signal with its manufacturer (communicative), `N` = it does not (non-communicative). -/
inductive Arrangement
  | S
  | N
  deriving DecidableEq, Repr

/-- Standing assumptions of §5 (p. 13) for two identical chains: `k > a/(4c)`, `k > 1/3`, `a > c`;
together with the positivity of the unit cost `c`, the signal accuracy `t` and the prior variance
`σsq = σ²` (§3, pp. 7–8), and the competition intensity `0 < γ < 1` (`γ_C ∈ [0,1)` on p. 7, with
`γ_C = 0` excluded). -/
def Standing (a c k γ t σsq : ℝ) : Prop :=
  0 < c ∧ c < a ∧ a / (4 * c) < k ∧ 1 / 3 < k ∧ 0 < γ ∧ γ < 1 ∧ 0 < t ∧ 0 < σsq

/-- Signal weight `tσ²/(1 + tσ²)` (p. 8): `E[θ | Y_i] = E[Y_j | Y_i] = sig · Y_i`. -/
noncomputable def sig (t σsq : ℝ) : ℝ := t * σsq / (1 + t * σsq)

/-- The signal term `tσ⁴/(tσ² + 1)` of the ex-ante profits (p. 17). -/
noncomputable def sigTerm (t σsq : ℝ) : ℝ := t * σsq ^ 2 / (t * σsq + 1)

/-- Lemma 2(a), p. 15: the response coefficient `C_i^{X_iX_j}` of retailer `i`'s equilibrium
quantity to its own signal `Y_i`, when chain `i` has arrangement `Xi` and chain `j` has `Xj`. -/
noncomputable def C (k γ t σsq : ℝ) : Arrangement → Arrangement → ℝ
  | .S, .S => k * (t * σsq) / ((4 * (t * σsq) + 4 + γ * (t * σsq)) * k - (t * σsq + 1))
  | .S, .N => (2 + (2 - γ) * (t * σsq)) * k * (t * σsq) /
      ((8 * (1 + t * σsq) ^ 2 - γ ^ 2 * (t * σsq) ^ 2) * k - 2 * (t * σsq + 1) ^ 2)
  | .N, .S => ((4 + 4 * (t * σsq) - γ * (t * σsq)) * k - (t * σsq + 1)) * (t * σsq) /
      ((8 * (t * σsq + 1) ^ 2 - γ ^ 2 * (t * σsq) ^ 2) * k - 2 * (t * σsq + 1) ^ 2)
  | .N, .N => t * σsq / (2 * (t * σsq + 1) + γ * (t * σsq))

/-- Intercept `k(a − c)/((γ_C + 4)k − 1)` of the equilibrium quantity (Lemma 2(a), p. 15). -/
noncomputable def qbar (a c k γ : ℝ) : ℝ := k * (a - c) / ((γ + 4) * k - 1)

/-- Retailer `i`'s best response (7) (`Xi = S`) and (9) (`Xi = N`), p. 14, written as a function of
`m = E[θ | Y_i]`, `e = E[q_j | Y_i]` and `E = E[q_j]`. -/
noncomputable def br (a c k γ : ℝ) : Arrangement → ℝ → ℝ → ℝ → ℝ
  | .S, m, e, _ => k / (4 * k - 1) * (a + m - γ * e - c)
  | .N, m, e, E => k / (4 * k - 1) * (a - c) + 1 / 2 * (m - γ * e + (2 * k - 1) / (4 * k - 1) * γ * E)

/-- Ex-ante profit `π^X_{R_i,C}(C_j)` of retailer `i` (p. 17) when chain `j`'s quantity responds
to `Y_j` with coefficient `Cj`. -/
noncomputable def piR (a c k γ t σsq : ℝ) : Arrangement → ℝ → ℝ
  | .S, Cj => k ^ 2 * (a - c) ^ 2 / (4 * k + k * γ - 1) ^ 2 +
      k ^ 2 / (4 * k - 1) ^ 2 * (1 - γ * Cj) ^ 2 * sigTerm t σsq
  | .N, Cj => k ^ 2 * (a - c) ^ 2 / (4 * k + k * γ - 1) ^ 2 +
      1 / 4 * (1 - γ * Cj) ^ 2 * sigTerm t σsq

/-- Ex-ante profit `π^X_{M_i,C}(C_j)` of manufacturer `i` (p. 17). -/
noncomputable def piM (a c k γ t σsq : ℝ) : Arrangement → ℝ → ℝ
  | .S, Cj => k * (4 * k - 1) * (a - c) ^ 2 / (2 * (4 * k + k * γ - 1) ^ 2) +
      k / (2 * (4 * k - 1)) * (1 - γ * Cj) ^ 2 * sigTerm t σsq
  | .N, _ => k * (4 * k - 1) * (a - c) ^ 2 / (2 * (4 * k + k * γ - 1) ^ 2)

/-- Ex-ante profit of supply chain `i`: `π^X_{i,C} = π^X_{R_i,C} + π^X_{M_i,C}` (p. 17). -/
noncomputable def piC (a c k γ t σsq : ℝ) (X : Arrangement) (Cj : ℝ) : ℝ :=
  piR a c k γ t σsq X Cj + piM a c k γ t σsq X Cj

/-- Equilibrium profit `Π^{X_iX_j}_{R_i,C} = π^{X_i}_{R_i,C}(C_j^{X_jX_i})` (p. 17). -/
noncomputable def PiR (a c k γ t σsq : ℝ) (Xi Xj : Arrangement) : ℝ :=
  piR a c k γ t σsq Xi (C k γ t σsq Xj Xi)

/-- Equilibrium profit `Π^{X_iX_j}_{M_i,C} = π^{X_i}_{M_i,C}(C_j^{X_jX_i})` (p. 17). -/
noncomputable def PiM (a c k γ t σsq : ℝ) (Xi Xj : Arrangement) : ℝ :=
  piM a c k γ t σsq Xi (C k γ t σsq Xj Xi)

/-- Equilibrium profit `Π^{X_iX_j}_{i,C} = π^{X_i}_{i,C}(C_j^{X_jX_i})` of supply chain `i` (p. 17). -/
noncomputable def PiC (a c k γ t σsq : ℝ) (Xi Xj : Arrangement) : ℝ :=
  piC a c k γ t σsq Xi (C k γ t σsq Xj Xi)

/-- Value of information sharing to chain `i`, `V^{X_j}_{i,C} = Π^{SX_j}_{i,C} − Π^{NX_j}_{i,C}`
(§5.2, p. 18). -/
noncomputable def V (a c k γ t σsq : ℝ) (Xj : Arrangement) : ℝ :=
  PiC a c k γ t σsq .S Xj - PiC a c k γ t σsq .N Xj

/-- Manufacturer `i`'s optimal side payment `m̂_i^{X_j}` to retailer `i` (§5.3, p. 21). -/
noncomputable def mhat (a c k γ t σsq : ℝ) (Xj : Arrangement) : ℝ :=
  if PiR a c k γ t σsq .N Xj > PiR a c k γ t σsq .S Xj then
    PiR a c k γ t σsq .N Xj - PiR a c k γ t σsq .S Xj
  else 0

/-- Manufacturer `i`'s stage-one payoff when chain `i` has arrangement `Xi` and chain `j` has `Xj`
(§5.3, pp. 20–21): `Π^{SX_j}_{M_i,C} − m̂_i^{X_j}` if `Xi = S`, and `Π^{NX_j}_{M_i,C}` if `Xi = N`. -/
noncomputable def payoff (a c k γ t σsq : ℝ) : Arrangement → Arrangement → ℝ
  | .S, Xj => PiM a c k γ t σsq .S Xj - mhat a c k γ t σsq Xj
  | .N, Xj => PiM a c k γ t σsq .N Xj

/-- The pure-strategy Nash equilibria `(X₁, X₂)` of the stage-one game between the two
manufacturers (Table 1, p. 21): manufacturer 1's payoff at `(X₁, X₂)` is `payoff X₁ X₂`, and
manufacturer 2's is `payoff X₂ X₁`. -/
def equilibria (a c k γ t σsq : ℝ) : Set (Arrangement × Arrangement) :=
  pureNashSet (fun X₁ X₂ => payoff a c k γ t σsq X₁ X₂) (fun X₁ X₂ => payoff a c k γ t σsq X₂ X₁)

end CompetingChains.Cournot


