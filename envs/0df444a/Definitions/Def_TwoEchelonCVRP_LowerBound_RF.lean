-- Prove2me | Definitions.Def_TwoEchelonCVRP_LowerBound_RF
-- name    : TwoEchelonCVRP_LowerBound_RF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T15:12:36.356348+00:00
-- url     : https://prove2.me/theorems/fc0efb2f-0ef3-45ce-a401-303cf46e7c24
-- title:
--   §3.1: the penalty system (12), relaxation RF (13)–(18), and reduced costs
-- statement:
--   Relaxation $RF$ of the 2E-CVRP is obtained from formulation $F$ by relaxing constraints (2)–(4) in a Lagrangean fashion, with penalties $\lambda_i \in \mathbb R$ ($i \in N_C$), $\mu_k \le 0$ ($k \in N_S$) and $\mu_0 \le 0$, and by introducing **marginal routing costs** $\beta_{ik}$ of serving customer $i$ from satellite $k$, required to satisfy
--   $$\sum_{i \in N_C} a_{ikl}\beta_{ik} \le c_{kl} - \sum_{i \in N_C} a_{ikl}\lambda_i - \mu_k - \mu_0, \qquad l \in \mathcal R_k,\ k \in N_S. \qquad (12)$$
--
--   With binary variables $\xi_{ik}$ (customer $i$ supplied from satellite $k$), binary $y_r$ and nonnegative integers $q_{kr}$ (zero for $k \notin R_r$), $RF$ is
--   $$z(RF(\beta,\lambda,\mu)) = \min \sum_{k \in N_S}\sum_{i \in N_C}\beta_{ik}\xi_{ik} + \sum_{r \in \mathcal M} g_r y_r + \sum_{i \in N_C}\lambda_i + \sum_{k \in N_S} m_k\mu_k + m^2\mu_0 \qquad (13)$$
--   subject to
--   1. (14) $\sum_{k} \xi_{ik} = 1$ for every customer $i$;
--   2. (15) $\sum_{r \in \mathcal M_k} q_{kr} = \sum_{i} q_i \xi_{ik}$ for every satellite $k$;
--   3. (16) $\sum_i q_i \xi_{ik} \le B_k$;
--   4. (17) constraints (6) and (8) of $F$ (and the integrality (10), (11)).
--
--   The **reduced cost** of a second-level route $l \in \mathcal R_k$ is
--   $$\tilde c_{kl} = c_{kl} - \sum_{i \in N_C} a_{ikl}(\beta_{ik} + \lambda_i) - \mu_k - \mu_0 .$$
--   Condition (12) says exactly that every reduced cost is nonnegative.
--
--   **Formalization Note** $z(RF)$ is the infimum of (13) over the feasible solutions, taken in the extended reals, so it is $+\infty$ when $RF$ is infeasible. $RF$ contains neither (3), (4), (5), (7) nor any bound tying a satellite's load to its second-level fleet. The penalty system is stated for every route of the family $\mathcal R$, with $k = \pi_l$.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 301, §3.1, (12)–(18) and Corollary 1 (reduced cost)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model

namespace TwoEchelonCVRP.LowerBound

variable {I : Instance}

/-- The penalty system (12) (§3.1, p. 301): for every second-level route `l ∈ 𝓡_k`
(`k = π_l`),
`∑_i a_{ikl} β_{ik} ≤ c_{kl} − ∑_i a_{ikl} λ_i − μ_k − μ_0`.
Here `β i k = β_{ik}`, `lam i = λ_i`, `μ k = μ_k`, `μ0 = μ_0`. -/
def SatisfiesPenalty (RS : RouteSystem I) (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ)
    (μ : Fin I.ns → ℝ) (μ0 : ℝ) : Prop :=
  ∀ l : RS.SR,
    ∑ i, (RS.a i l : ℝ) * β i (RS.sat l)
      ≤ RS.c l - ∑ i, (RS.a i l : ℝ) * lam i - μ (RS.sat l) - μ0

/-- The reduced cost of second-level route `l ∈ 𝓡_k` (Corollary 1, p. 301):
`c̃_{kl} = c_{kl} − ∑_i a_{ikl}(β_{ik} + λ_i) − μ_k − μ_0`. -/
def reducedCost (RS : RouteSystem I) (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ)
    (μ : Fin I.ns → ℝ) (μ0 : ℝ) (l : RS.SR) : ℝ :=
  RS.c l - ∑ i, (RS.a i l : ℝ) * (β i (RS.sat l) + lam i) - μ (RS.sat l) - μ0

/-- The variables of relaxation RF: `ξ i k = ξ_{ik}` (customer `i` supplied from satellite `k`),
`y r = y_r`, `qd r k = q_{kr}`; (10), (11), (18) are carried by the types. -/
structure SolRF (RS : RouteSystem I) where
  ξ : Fin I.nc → Fin I.ns → Bool
  y : RS.FR → Bool
  qd : RS.FR → Fin I.ns → ℕ

/-- `∑_{i ∈ N_C} q_i ξ_{ik}`: the demand assigned to satellite `k` by an RF solution. -/
def SolRF.load {RS : RouteSystem I} (σ : SolRF RS) (k : Fin I.ns) : ℕ :=
  ∑ i, I.q i * (σ.ξ i k).toNat

/-- Feasibility for relaxation RF (§3.1, p. 301): (14), (15), (16), and (6), (8) of F, with the
convention `q_{kr} = 0` for `k ∉ R_r` of F. -/
def IsFeasibleRF (RS : RouteSystem I) (σ : SolRF RS) : Prop :=
  -- (14): every customer is assigned to exactly one satellite
  (∀ i, ∑ k, (σ.ξ i k).toNat = 1) ∧
  -- (15): flow balance at satellite `k`
  (∀ k, ∑ r ∈ Finset.univ.filter (fun r => k ∈ RS.Rsat r), σ.qd r k = σ.load k) ∧
  -- (16): satellite capacity
  (∀ k, σ.load k ≤ I.B k) ∧
  -- (6): at most `m^1` first-level routes
  (∑ r, (σ.y r).toNat ≤ I.m1) ∧
  -- (8): first-level capacity
  (∀ r, ∑ k ∈ RS.Rsat r, σ.qd r k ≤ I.Q1 * (σ.y r).toNat) ∧
  -- convention of F: `q_{kr} = 0` for `k ∉ R_r`
  (∀ r k, k ∉ RS.Rsat r → σ.qd r k = 0)

/-- The constant term `∑_i λ_i + ∑_k m_k μ_k + m^2 μ_0` shared by (13) and (19). -/
def penaltyConst (I : Instance) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ) : ℝ :=
  ∑ i, lam i + ∑ k, (I.m k : ℝ) * μ k + (I.m2 : ℝ) * μ0

/-- The objective (13) of RF. -/
def objRF (RS : RouteSystem I) (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ)
    (μ : Fin I.ns → ℝ) (μ0 : ℝ) (σ : SolRF RS) : ℝ :=
  ∑ k, ∑ i, β i k * ((σ.ξ i k).toNat : ℝ) + ∑ r, RS.g r * ((σ.y r).toNat : ℝ)
    + penaltyConst I lam μ μ0

/-- `z(RF(β, λ, μ))`: the optimal value of RF, in `EReal` (`⊤` when RF is infeasible). -/
noncomputable def zRF (RS : RouteSystem I) (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ)
    (μ : Fin I.ns → ℝ) (μ0 : ℝ) : EReal :=
  ⨅ (σ : SolRF RS) (_ : IsFeasibleRF RS σ), ((objRF RS β lam μ μ0 σ : ℝ) : EReal)

end TwoEchelonCVRP.LowerBound


