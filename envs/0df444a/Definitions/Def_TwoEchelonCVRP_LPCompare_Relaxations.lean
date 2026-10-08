-- Prove2me | Definitions.Def_TwoEchelonCVRP_LPCompare_Relaxations
-- name    : TwoEchelonCVRP_LPCompare_Relaxations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:54.537724+00:00
-- url     : https://prove2.me/theorems/ae2d7338-04cd-4de4-a739-603577129030
-- title:
--   §3–§3.1: the LP relaxation LF, the penalty system (12), and the relaxation RF (13)–(18)
-- statement:
--   Three objects built on formulation $F$ of the 2E-CVRP.
--
--   **The LP relaxation $LF$** (§3). Replace the integrality requirements of $F$ by $0 \le x_{kl} \le 1$, $0 \le y_r \le 1$, $q_{kr} \ge 0$ (keeping $q_{kr} = 0$ for $k \notin R_r$), with all variables real and constraints (2)–(8) unchanged. Its value $z(LF) \in \mathbb{R} \cup \{+\infty\}$ is the infimum of the objective (1) over the feasible points, $+\infty$ when there is none. A point is an *optimal* $LF$ solution when it is feasible and no feasible point is cheaper.
--
--   **Admissible penalties** (§3.1, (12)). Penalties $\lambda \in \mathbb{R}^{N_C}$, $\mu = (\mu_k)_{k \in N_S}$ with $\mu_k \le 0$, $\mu_0 \le 0$, and marginal routing costs $\beta_{ik}$ are admissible when, for every second-level route $l$ with satellite $k = \pi_l$,
--   $$\sum_{i \in N_C} a_{ikl}\,\beta_{ik} \le c_{kl} - \sum_{i \in N_C} a_{ikl}\,\lambda_i - \mu_k - \mu_0. \tag{12}$$
--
--   **The relaxation $RF(\beta,\lambda,\mu)$** (§3.1). With binary $\xi_{ik}$ (customer $i$ supplied from satellite $k$), binary $y_r$ and nonnegative integers $q_{kr}$ ($q_{kr}=0$ for $k \notin R_r$), minimize
--   $$\sum_{k}\sum_{i} \beta_{ik}\xi_{ik} + \sum_r g_r y_r + \sum_i \lambda_i + \sum_k m_k \mu_k + m^2 \mu_0 \tag{13}$$
--   subject to $\sum_k \xi_{ik} = 1$ (14), $\sum_{r \in \mathcal M_k} q_{kr} = \sum_i q_i \xi_{ik}$ (15), $\sum_i q_i \xi_{ik} \le B_k$ (16), and $\sum_r y_r \le m^1$, $\sum_{k \in R_r} q_{kr} \le Q_1 y_r$ ((6), (8)). Its value $z(RF(\beta,\lambda,\mu))$ is the minimum, $+\infty$ when $RF$ is infeasible.
--
--   $RF$ arises from $F$ by relaxing (2)–(4) in a Lagrangean fashion and replacing the route variables by customer-to-satellite assignments; $LF$ is the usual linear relaxation. The mission compares the two bounds.
--
--   **Formalization Note.** Both values are taken in `EReal` as infima over the feasible set, so an infeasible problem has value $+\infty$. $RF$ has finitely many feasible solutions, so its infimum is a minimum when finite. $RF$ restates (6), (8) and (11) explicitly rather than referring to $F$.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 301, §3 (definition of LF) and §3.1, Eqs. (12)–(18)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LPCompare_Model

namespace TwoEchelonCVRP.LPCompare

open Finset

/-! ### The LP relaxation `LF` (§3, p. 301) -/

/-- A point of the LP relaxation `LF`: real `x_{kl}`, `y_r`, `q_{kr}`. -/
structure LFPoint {I : Instance} (RS : RouteSystem I) where
  x : RS.SR → ℝ
  y : RS.FR → ℝ
  qd : RS.FR → Fin I.ns → ℝ

/-- Feasibility for `LF`, the LP relaxation of `F`: constraints (2)–(8) of §2.1 over the reals,
with (9)–(11) replaced by `0 ≤ x_{kl} ≤ 1`, `0 ≤ y_r ≤ 1`, `q_{kr} ≥ 0`, and `q_{kr} = 0` for
`k ∉ R_r` kept. -/
def IsFeasibleLF {I : Instance} {RS : RouteSystem I} (p : LFPoint RS) : Prop :=
  -- (2)
  (∀ i, ∑ l ∈ univ.filter (fun l => i ∈ RS.cust l), p.x l = 1) ∧
  -- (3)
  (∀ k, ∑ l ∈ univ.filter (fun l => RS.sat l = k), p.x l ≤ (I.m k : ℝ)) ∧
  -- (4)
  (∑ l, p.x l ≤ (I.m2 : ℝ)) ∧
  -- (5)
  (∀ k, ∑ l ∈ univ.filter (fun l => RS.sat l = k), (RS.w l : ℝ) * p.x l ≤ (I.B k : ℝ)) ∧
  -- (6)
  (∑ r, p.y r ≤ (I.m1 : ℝ)) ∧
  -- (7)
  (∀ k, ∑ r ∈ univ.filter (fun r => k ∈ RS.R1 r), p.qd r k
      = ∑ l ∈ univ.filter (fun l => RS.sat l = k), (RS.w l : ℝ) * p.x l) ∧
  -- (8)
  (∀ r, ∑ k ∈ RS.R1 r, p.qd r k ≤ (I.Q1 : ℝ) * p.y r) ∧
  -- (9)–(10) relaxed
  (∀ l, 0 ≤ p.x l ∧ p.x l ≤ 1) ∧
  (∀ r, 0 ≤ p.y r ∧ p.y r ≤ 1) ∧
  -- (11) relaxed, `q_{kr}` defined only for `k ∈ R_r`
  (∀ r k, 0 ≤ p.qd r k) ∧
  (∀ r k, k ∉ RS.R1 r → p.qd r k = 0)

/-- The objective (1) evaluated at an `LF` point. -/
def costLF {I : Instance} {RS : RouteSystem I} (p : LFPoint RS) : ℝ :=
  ∑ l, RS.c l * p.x l + ∑ r, RS.g r * p.y r

/-- `z(LF)`: the infimum of (1) over the `LF`-feasible points, in `EReal` (`⊤` when `LF`
is infeasible). -/
noncomputable def zLF {I : Instance} (RS : RouteSystem I) : EReal :=
  ⨅ p : {p : LFPoint RS // IsFeasibleLF p}, ((costLF p.1 : ℝ) : EReal)

/-- An optimal `LF` solution: feasible, and of cost at most that of every feasible point. -/
def IsOptimalLF {I : Instance} {RS : RouteSystem I} (p : LFPoint RS) : Prop :=
  IsFeasibleLF p ∧ ∀ p' : LFPoint RS, IsFeasibleLF p' → costLF p ≤ costLF p'

/-! ### The penalty system (12) and the relaxation `RF` (§3.1, p. 301) -/

/-- Inequalities (12): for every second-level route `l` with satellite `k = π_l`,
`∑_i a_{ikl} β_{ik} ≤ c_{kl} − ∑_i a_{ikl} λ_i − μ_k − μ_0`. -/
def SatisfiesPenalty {I : Instance} (RS : RouteSystem I) (beta : Fin I.nc → Fin I.ns → ℝ)
    (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ) : Prop :=
  ∀ l : RS.SR, ∑ i, (RS.a i l : ℝ) * beta i (RS.sat l)
    ≤ RS.c l - ∑ i, (RS.a i l : ℝ) * lam i - mu (RS.sat l) - mu0

/-- An admissible choice of penalties: `λ ∈ ℝ^{N_C}` arbitrary, `μ ∈ ℝ_−^{N_S+1}`
(`μ_k ≤ 0` for every satellite and `μ_0 ≤ 0`), and `β` a solution of (12). -/
def Admissible {I : Instance} (RS : RouteSystem I) (beta : Fin I.nc → Fin I.ns → ℝ)
    (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ) : Prop :=
  (∀ k, mu k ≤ 0) ∧ mu0 ≤ 0 ∧ SatisfiesPenalty RS beta lam mu mu0

/-- A candidate solution of `RF`: binary assignments `ξ_{ik}`, binary `y_r`, and nonnegative
integer deliveries `q_{kr}`. -/
structure RFSol {I : Instance} (RS : RouteSystem I) where
  xi : Fin I.nc → Fin I.ns → Bool
  y : RS.FR → Bool
  qd : RS.FR → Fin I.ns → ℕ

/-- Feasibility for `RF`: constraints (14), (15), (16), and (17) = (6), (8), (10), (11);
(10), (18) and the integrality in (11) are the types (`Bool`, `ℕ`). -/
def IsFeasibleRF {I : Instance} {RS : RouteSystem I} (s : RFSol RS) : Prop :=
  -- (14) every customer is assigned to exactly one satellite
  (∀ i, ∑ k, (s.xi i k).toNat = 1) ∧
  -- (15) the delivery to each satellite equals the demand assigned to it
  (∀ k, ∑ r ∈ univ.filter (fun r => k ∈ RS.R1 r), s.qd r k
      = ∑ i, I.q i * (s.xi i k).toNat) ∧
  -- (16) satellite capacity
  (∀ k, ∑ i, I.q i * (s.xi i k).toNat ≤ I.B k) ∧
  -- (6) at most `m¹` first-level routes
  (∑ r, (s.y r).toNat ≤ I.m1) ∧
  -- (8) first-level capacity
  (∀ r, ∑ k ∈ RS.R1 r, s.qd r k ≤ I.Q1 * (s.y r).toNat) ∧
  -- (11) `q_{kr}` is defined only for `k ∈ R_r`
  (∀ r k, k ∉ RS.R1 r → s.qd r k = 0)

/-- The objective (13) of `RF(β, λ, μ)`. -/
def objRF {I : Instance} {RS : RouteSystem I} (beta : Fin I.nc → Fin I.ns → ℝ)
    (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ) (s : RFSol RS) : ℝ :=
  ∑ k, ∑ i, beta i k * ((s.xi i k).toNat : ℝ) + ∑ r, RS.g r * ((s.y r).toNat : ℝ)
    + ∑ i, lam i + ∑ k, (I.m k : ℝ) * mu k + (I.m2 : ℝ) * mu0

/-- `z(RF(β, λ, μ))`: the minimum of (13) over the `RF`-feasible solutions, in `EReal`
(`⊤` when `RF` is infeasible). -/
noncomputable def zRF {I : Instance} (RS : RouteSystem I) (beta : Fin I.nc → Fin I.ns → ℝ)
    (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ) : EReal :=
  ⨅ s : {s : RFSol RS // IsFeasibleRF s}, ((objRF beta lam mu mu0 s.1 : ℝ) : EReal)

end TwoEchelonCVRP.LPCompare


