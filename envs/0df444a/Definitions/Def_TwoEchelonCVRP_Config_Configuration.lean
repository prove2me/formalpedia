-- Prove2me | Definitions.Def_TwoEchelonCVRP_Config_Configuration
-- name    : TwoEchelonCVRP_Config_Configuration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:10.180065+00:00
-- url     : https://prove2.me/theorems/d5627c45-6efd-4c33-99f2-193a60de6b7c
-- title:
--   §5: configurations 𝒫, N_S(M), M_k, U(M), problem F(M) and z(F(M))
-- statement:
--   This file defines the configuration reformulation of §5 of Baldacci, Mingozzi, Roberti and Wolfler Calvo (2013), on top of the 2E-CVRP model of the mission.
--
--   A **configuration** is a set $M\subseteq\mathcal M$ of first-level routes with
--   $$|M|\,Q_1\ge q_{\mathrm{tot}},\qquad |M|\le m^1 ;$$
--   $\mathcal P$ is the (finite) set of all configurations. For $M\subseteq\mathcal M$, $N_S(M)=\bigcup_{r\in M}R_r$ is the set of satellites it visits, $M_k=\{r\in M: k\in R_r\}$ the routes of $M$ through satellite $k$, and $U(M)=\sum_{r\in M} g_r$ its first-level cost. The configuration of a solution of $F$ is the set of first-level routes with $y_r=1$.
--
--   **Problem $F(M)$.** Its variables are binary $x_{kl}$ for the second-level routes of the satellites $k\in N_S(M)$ only, and **real** deliveries $q_{kr}\ge 0$ for $r\in M$, $k\in R_r$. It minimizes $\sum_{k\in N_S(M)}\sum_{l\in\mathcal R_k} c_{kl}x_{kl}$ subject to
--   1. $\sum_{k\in N_S(M)}\sum_{l\in\mathcal R_{ik}} x_{kl}=1$ for every customer $i$;
--   2. $\sum_{l\in\mathcal R_k}x_{kl}\le m_k$ for $k\in N_S(M)$;
--   3. $\sum_{k\in N_S(M)}\sum_{l\in\mathcal R_k}x_{kl}\le m^2$;
--   4. $\sum_{l\in\mathcal R_k}w_{kl}x_{kl}\le B_k$ for $k\in N_S(M)$;
--   5. $\sum_{r\in M_k}q_{kr}=\sum_{l\in\mathcal R_k}w_{kl}x_{kl}$ for $k\in N_S(M)$;
--   6. $\sum_{k\in R_r}q_{kr}\le Q_1$ for $r\in M$.
--
--   Its optimal value $z(F(M))$ is $+\infty$ when $F(M)$ has no feasible solution, as the paper assumes.
--
--   $F(M)$ is the second-level problem left once the first-level routes are fixed to $M$; the method of the paper enumerates $\mathcal P$, prunes it, and solves $F(M)$ for the surviving configurations.
--
--   **Formalization Note** A configuration is a `Finset` of route indices and $\mathcal P$ is `configs`, the subsets satisfying `InP`. A solution of $F(M)$ assigns `x` to every second-level route, with the constraint that a used route belongs to a satellite of $N_S(M)$ (the paper's variables exist only there); its deliveries `qd r k` are real, as printed (in $F$ they are integers), and are only read for $r\in M$, $k\in R_r$. $z(F(M))$ is an infimum in `EReal`, `⊤` on an infeasible problem.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 305, §5, the definitions of 𝒫, N_S(M), M_k, U(M) and problem F(M)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Model

namespace TwoEchelonCVRP.Config

variable {I : Instance}

/-- A configuration `M ⊆ 𝓜` belongs to `𝒫 = {M ⊆ 𝓜 : |M| Q_1 ≥ q_tot, |M| ≤ m^1}` (§5, p. 305). -/
def InP (RS : RouteSystem I) (M : Finset RS.FR) : Prop :=
  I.qtot ≤ M.card * I.Q1 ∧ M.card ≤ I.m1

instance (RS : RouteSystem I) (M : Finset RS.FR) : Decidable (InP RS M) := by
  unfold InP; infer_instance

/-- The finite set `𝒫` of all configurations. -/
def configs (RS : RouteSystem I) : Finset (Finset RS.FR) :=
  (Finset.univ : Finset (Finset RS.FR)).filter (fun M => InP RS M)

/-- `N_S(M) = ⋃_{r ∈ M} R_r`: the satellites visited by the routes of `M`. -/
def NS (RS : RouteSystem I) (M : Finset RS.FR) : Finset (Fin I.ns) :=
  M.biUnion RS.Rsat

/-- `M_k = M ∩ 𝓜_k`: the routes of `M` visiting satellite `k`. -/
def Mk (RS : RouteSystem I) (M : Finset RS.FR) (k : Fin I.ns) : Finset RS.FR :=
  M.filter (fun r => k ∈ RS.Rsat r)

/-- `U(M) = ∑_{r ∈ M} g_r`: the cost of the first-level routes of `M`. -/
def U (RS : RouteSystem I) (M : Finset RS.FR) : ℝ :=
  ∑ r ∈ M, RS.g r

/-- The configuration of a solution of F: the set of first-level routes with `y_r = 1`. -/
def conf {RS : RouteSystem I} (s : SolF RS) : Finset RS.FR :=
  Finset.univ.filter (fun r => s.y r = true)

/-- A choice of the variables of problem F(M): `x l = x_{kl}` and the **real** deliveries
`qd r k = q_{kr}` (F(M) has `q_{kr} ≥ 0`, not `q_{kr} ∈ ℤ_+`). -/
structure SolFM (RS : RouteSystem I) where
  x : RS.SR → Bool
  qd : RS.FR → Fin I.ns → ℝ

/-- Feasibility for problem F(M) (§5, p. 305). The variables `x_{kl}` exist only for satellites
`k ∈ N_S(M)`; a route of another satellite is not used. The deliveries `q_{kr}` are used only for
`r ∈ M`, `k ∈ R_r`. -/
def IsFeasibleFM (RS : RouteSystem I) (M : Finset RS.FR) (t : SolFM RS) : Prop :=
  -- `x_{kl}` is defined only for `k ∈ N_S(M)`
  (∀ l, t.x l = true → RS.sat l ∈ NS RS M) ∧
  -- every customer is served by exactly one used route of a satellite of `N_S(M)`
  (∀ i, ∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ NS RS M ∧ i ∈ RS.tour2 l),
      (t.x l).toNat = 1) ∧
  -- at most `m_k` routes at satellite `k ∈ N_S(M)`
  (∀ k ∈ NS RS M, ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (t.x l).toNat ≤ I.m k) ∧
  -- at most `m^2` second-level routes in total
  (∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ NS RS M), (t.x l).toNat ≤ I.m2) ∧
  -- satellite capacity, `k ∈ N_S(M)`
  (∀ k ∈ NS RS M,
      ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), RS.w l * (t.x l).toNat ≤ I.B k) ∧
  -- flow balance at `k ∈ N_S(M)`: `∑_{r ∈ M_k} q_{kr} = ∑_{l ∈ 𝓡_k} w_{kl} x_{kl}`
  (∀ k ∈ NS RS M, ∑ r ∈ Mk RS M k, t.qd r k
      = ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), ((RS.w l * (t.x l).toNat : ℕ) : ℝ)) ∧
  -- first-level capacity `∑_{k ∈ R_r} q_{kr} ≤ Q_1`, `r ∈ M`
  (∀ r ∈ M, ∑ k ∈ RS.Rsat r, t.qd r k ≤ (I.Q1 : ℝ)) ∧
  -- `q_{kr} ≥ 0`, `k ∈ R_r`, `r ∈ M`
  (∀ r ∈ M, ∀ k ∈ RS.Rsat r, 0 ≤ t.qd r k)

/-- The objective of F(M): `∑_{k ∈ N_S(M)} ∑_{l ∈ 𝓡_k} c_{kl} x_{kl}`. -/
def costFM (RS : RouteSystem I) (M : Finset RS.FR) (t : SolFM RS) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l => RS.sat l ∈ NS RS M), RS.c l * ((t.x l).toNat : ℝ)

/-- `z(F(M))`, in `EReal`: the infimum of the F(M) objective over its feasible solutions, `⊤`
(the paper's `z(F(M)) = ∞`) when F(M) has no feasible solution. -/
noncomputable def zFM (RS : RouteSystem I) (M : Finset RS.FR) : EReal :=
  ⨅ (t : SolFM RS) (_ : IsFeasibleFM RS M t), ((costFM RS M t : ℝ) : EReal)

end TwoEchelonCVRP.Config


