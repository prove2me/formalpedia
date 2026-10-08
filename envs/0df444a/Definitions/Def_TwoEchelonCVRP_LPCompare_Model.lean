-- Prove2me | Definitions.Def_TwoEchelonCVRP_LPCompare_Model
-- name    : TwoEchelonCVRP_LPCompare_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:06:58.083094+00:00
-- url     : https://prove2.me/theorems/5e33ab05-1707-4280-9ab8-b5f7b88fcc48
-- title:
--   §2–§2.1: the 2E-CVRP instance, route families, and formulation F (1)–(11)
-- statement:
--   This file sets up the **two-echelon capacitated vehicle routing problem** (2E-CVRP) of Baldacci, Mingozzi, Roberti and Wolfler Calvo and its set-partitioning formulation $F$.
--
--   **Instance.** The vertices are a depot $0$, $n_s$ satellites $N_S$ and $n_c$ customers $N_C$. A symmetric travel cost $d_{uv}$ is given on pairs of vertices; it is the paper's matrix *after* the fixed vehicle costs have been folded in ($\tfrac12 U_1$ added to $d_{0k}$, $\tfrac12 U_2$ added to $d_{ki}$). Customer $i$ has a demand $q_i \in \mathbb{Z}_{>0}$. First-level vehicles have capacity $Q_1$, second-level vehicles capacity $Q_2$ with $0 < Q_2 < Q_1$. At most $m^1$ first-level vehicles may be used; satellite $k$ hosts $m_k$ second-level vehicles, and at most $m^2 \le \sum_k m_k$ second-level vehicles may be used overall. Satellite $k$ has capacity $B_k$ and unit handling cost $H_k$.
--
--   **Routes.** A first-level route $r \in \mathcal M$ leaves the depot, visits a nonempty list of distinct satellites, and returns; $R_r$ is its set of satellites and its cost $g_r$ is the cost of the closed walk $0 \to s_1 \to \dots \to s_p \to 0$ (so $(0,k,0)$ costs $2d_{0k}$). A second-level route $l \in \mathcal R$ leaves a satellite $\pi_l$, visits a nonempty list of distinct customers $R_{kl}$, and returns; its load is $w_{kl} = \sum_{i \in R_{kl}} q_i \le Q_2$, $a_{ikl}$ counts its visits to customer $i$, and its cost is
--   $$c_{kl} = (\text{closed-walk cost from } \pi_l) + H_k\, w_{kl}, \qquad k = \pi_l.$$
--   The families $\mathcal M$ and $\mathcal R$ are arbitrary finite families of such routes (repetitions allowed).
--
--   **Formulation $F$.** With binary $x_{kl}$, binary $y_r$ and nonnegative integers $q_{kr}$ ($q_{kr}=0$ for $k \notin R_r$), $F$ minimizes $\sum_{l} c_{kl} x_{kl} + \sum_r g_r y_r$ (1) subject to: every customer is covered by exactly one chosen route (2); at most $m_k$ routes at satellite $k$ (3); at most $m^2$ second-level routes (4); $\sum_{l \in \mathcal R_k} w_{kl} x_{kl} \le B_k$ (5); $\sum_r y_r \le m^1$ (6); $\sum_{r \in \mathcal M_k} q_{kr} = \sum_{l \in \mathcal R_k} w_{kl} x_{kl}$ (7); $\sum_{k \in R_r} q_{kr} \le Q_1 y_r$ (8).
--
--   These objects are shared by the LP relaxation $LF$ and the relaxation $RF$ of the companion definition file.
--
--   **Formalization Note.** Satellites are `Fin ns` and customers `Fin nc` (0-based). Costs are computed from $d$ along closed walks, as the paper's §2.2 implies. The triangle inequality is not assumed (it is not used and does not survive the fixed-cost modification). Demands are taken positive, reading "customer $i$ requires $q_i$ units". The route families are arbitrary finite families, which generalizes the paper's "all routes".
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), pp. 299–300, §2 and §2.1, formulation F (1)–(11)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model

namespace TwoEchelonCVRP.LPCompare

open Finset

/-- A 2E-CVRP instance (§2, p. 299). The travel cost `d` is the matrix *after* the paper's
modification that folds the fixed costs in: `(1/2)U₁` added to `d_{0k}` and `(1/2)U₂` added to
`d_{ki}`; the fixed costs `U₁, U₂` therefore do not appear separately. The triangle inequality
is not assumed (it is not needed and does not survive that modification in general).
Customer demands are positive (`q_pos`), the reading of "each customer requires `q_i` units". -/
structure Instance where
  /-- Number of satellites `n_s`. -/
  ns : ℕ
  /-- Number of customers `n_c`. -/
  nc : ℕ
  /-- Symmetric travel cost `d_{ij}` (fixed costs already folded in). -/
  d : TwoEchelonCVRP.LowerBound.Vertex ns nc → TwoEchelonCVRP.LowerBound.Vertex ns nc → ℝ
  d_symm : ∀ u v, d u v = d v u
  /-- Customer demands `q_i`. -/
  q : Fin nc → ℕ
  q_pos : ∀ i, 0 < q i
  /-- First-level vehicle capacity `Q₁`. -/
  Q1 : ℕ
  /-- Second-level vehicle capacity `Q₂`. -/
  Q2 : ℕ
  Q2_pos : 0 < Q2
  Q2_lt_Q1 : Q2 < Q1
  /-- Number `m¹` of first-level vehicles. -/
  m1 : ℕ
  /-- Global bound `m²` on the number of second-level vehicles. -/
  m2 : ℕ
  /-- Number `m_k` of second-level vehicles at satellite `k`. -/
  m : Fin ns → ℕ
  m2_le : m2 ≤ ∑ k, m k
  /-- Satellite capacity `B_k`. -/
  B : Fin ns → ℕ
  /-- Unit handling cost `H_k` at satellite `k`. -/
  H : Fin ns → ℝ

/-- Total demand `q_tot = ∑_{i ∈ N_C} q_i`. -/
def Instance.qtot (I : Instance) : ℕ := ∑ i, I.q i

/-- A route system over an instance (§2.1, pp. 299–300): a finite family `𝓜` of first-level
routes (index type `FR`; repeated routes are allowed, which represents the paper's copies of
single-satellite routes) and a finite family `𝓡` of second-level routes (index type `SR`).
A first-level route `r` is the list of satellites it visits after leaving the depot, in order;
a second-level route `l` starts and ends at satellite `sat l` (the paper's `π_l`) and visits
the customers `tour2 l` in order. Routes are elementary and nonempty, and every second-level
route respects the capacity `Q₂`. The families are arbitrary (not necessarily *all* routes). -/
structure RouteSystem (I : Instance) where
  /-- Index type of the first-level routes `𝓜`. -/
  FR : Type
  [frFintype : Fintype FR]
  [frDecEq : DecidableEq FR]
  /-- The satellites visited by first-level route `r`, in visiting order. -/
  tour1 : FR → List (Fin I.ns)
  tour1_ne : ∀ r, tour1 r ≠ []
  tour1_nodup : ∀ r, (tour1 r).Nodup
  /-- Index type of the second-level routes `𝓡`. -/
  SR : Type
  [srFintype : Fintype SR]
  [srDecEq : DecidableEq SR]
  /-- The satellite `π_l` of second-level route `l`. -/
  sat : SR → Fin I.ns
  /-- The customers visited by second-level route `l`, in visiting order. -/
  tour2 : SR → List (Fin I.nc)
  tour2_ne : ∀ l, tour2 l ≠ []
  tour2_nodup : ∀ l, (tour2 l).Nodup
  load_le : ∀ l, ∑ i ∈ (tour2 l).toFinset, I.q i ≤ I.Q2

attribute [instance] RouteSystem.frFintype RouteSystem.frDecEq
  RouteSystem.srFintype RouteSystem.srDecEq

namespace RouteSystem

variable {I : Instance} (RS : RouteSystem I)

/-- `R_r`: the satellites visited by first-level route `r`. -/
def R1 (r : RS.FR) : Finset (Fin I.ns) := (RS.tour1 r).toFinset

/-- `g_r`: the cost of first-level route `r`, the closed walk from the depot through its
satellites (so the route `(0, k, 0)` costs `2 d_{0k}`). -/
def g (r : RS.FR) : ℝ :=
  TwoEchelonCVRP.LowerBound.closedWalkCost I.d TwoEchelonCVRP.LowerBound.Vertex.depot ((RS.tour1 r).map TwoEchelonCVRP.LowerBound.Vertex.sat)

/-- `R_{kl}`: the customers visited by second-level route `l`. -/
def cust (l : RS.SR) : Finset (Fin I.nc) := (RS.tour2 l).toFinset

/-- `a_{ikl}`: the number of times route `l` visits customer `i`. -/
def a (i : Fin I.nc) (l : RS.SR) : ℕ := (RS.tour2 l).count i

/-- `w_{kl} = ∑_{i ∈ R_{kl}} q_i`: the load of second-level route `l`. -/
def w (l : RS.SR) : ℕ := ∑ i ∈ RS.cust l, I.q i

/-- `c_{kl} = ∑_{{i,j} ∈ E(R_{kl})} d_{ij} + H_k w_{kl}` with `k = π_l`: the closed-walk cost
from the satellite through the route's customers plus the handling cost. -/
def c (l : RS.SR) : ℝ :=
  TwoEchelonCVRP.LowerBound.closedWalkCost I.d (TwoEchelonCVRP.LowerBound.Vertex.sat (RS.sat l)) ((RS.tour2 l).map TwoEchelonCVRP.LowerBound.Vertex.cust)
    + I.H (RS.sat l) * (RS.w l : ℝ)

end RouteSystem

/-- A candidate solution of formulation `F`: binary `x_{kl}` (one per second-level route,
`k = π_l`), binary `y_r`, and nonnegative integer deliveries `q_{kr}`. -/
structure FSol {I : Instance} (RS : RouteSystem I) where
  x : RS.SR → Bool
  y : RS.FR → Bool
  qd : RS.FR → Fin I.ns → ℕ

/-- Feasibility for formulation `F`, constraints (2)–(11) of §2.1 (p. 300); (9)–(11) are
the types (`Bool`, `ℕ`) plus `q_{kr} = 0` for `k ∉ R_r`. -/
def IsFeasibleF {I : Instance} {RS : RouteSystem I} (s : FSol RS) : Prop :=
  -- (2) every customer is served by exactly one chosen route
  (∀ i, ∑ l ∈ univ.filter (fun l => i ∈ RS.cust l), (s.x l).toNat = 1) ∧
  -- (3) at most `m_k` routes at satellite `k`
  (∀ k, ∑ l ∈ univ.filter (fun l => RS.sat l = k), (s.x l).toNat ≤ I.m k) ∧
  -- (4) at most `m²` second-level routes
  (∑ l, (s.x l).toNat ≤ I.m2) ∧
  -- (5) satellite capacity
  (∀ k, ∑ l ∈ univ.filter (fun l => RS.sat l = k), RS.w l * (s.x l).toNat ≤ I.B k) ∧
  -- (6) at most `m¹` first-level routes
  (∑ r, (s.y r).toNat ≤ I.m1) ∧
  -- (7) flow balance at each satellite
  (∀ k, ∑ r ∈ univ.filter (fun r => k ∈ RS.R1 r), s.qd r k
      = ∑ l ∈ univ.filter (fun l => RS.sat l = k), RS.w l * (s.x l).toNat) ∧
  -- (8) first-level capacity
  (∀ r, ∑ k ∈ RS.R1 r, s.qd r k ≤ I.Q1 * (s.y r).toNat) ∧
  -- (11) `q_{kr}` is defined only for `k ∈ R_r`
  (∀ r k, k ∉ RS.R1 r → s.qd r k = 0)

/-- The objective (1) of `F`. -/
def costF {I : Instance} {RS : RouteSystem I} (s : FSol RS) : ℝ :=
  ∑ l, RS.c l * ((s.x l).toNat : ℝ) + ∑ r, RS.g r * ((s.y r).toNat : ℝ)

end TwoEchelonCVRP.LPCompare


