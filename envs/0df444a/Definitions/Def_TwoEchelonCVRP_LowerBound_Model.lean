-- Prove2me | Definitions.Def_TwoEchelonCVRP_LowerBound_Model
-- name    : TwoEchelonCVRP_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T15:11:45.92406+00:00
-- url     : https://prove2.me/theorems/f5c55179-abac-4edb-89d4-089fede76e97
-- title:
--   §2–§2.1: the 2E-CVRP instance, route families, and formulation F (1)–(11)
-- statement:
--   This file sets up the **two-echelon capacitated vehicle routing problem** (2E-CVRP) of Baldacci, Mingozzi, Roberti and Wolfler Calvo (2013), together with its set-partitioning formulation $F$.
--
--   **Instance.** The vertex set is $N = \{0\} \cup N_S \cup N_C$: the depot $0$, the $n_s$ satellites $N_S$ and the $n_c$ customers $N_C$. A symmetric travel cost $d_{ij}$ is given; following the paper, the vehicle fixed costs are already folded into $d$ ($U_1/2$ added to every $d_{0k}$ and $U_2/2$ to every $d_{ki}$). Customer $i$ has a positive integer demand $q_i$, and $q_{\mathrm{tot}} = \sum_{i \in N_C} q_i$. There are $m^1$ first-level vehicles of capacity $Q_1$ at the depot; satellite $k$ has $m_k$ second-level vehicles of capacity $Q_2 < Q_1$, a capacity $B_k$ and a handling cost $H_k$ per unit; at most $m^2 \le \sum_k m_k$ second-level vehicles may be used in total.
--
--   **Routes.** A first-level route $r \in \mathcal M$ leaves the depot, visits a nonempty list of distinct satellites $R_r$ and returns; its cost $g_r$ is the sum of $d$ along this closed walk. A second-level route $l \in \mathcal R_k$ leaves satellite $k = \pi_l$, visits a nonempty list of distinct customers $R_{kl}$ (a simple cycle) and returns; its load is $w_{kl} = \sum_{i \in R_{kl}} q_i \le Q_2$ and its cost is
--   $$c_{kl} = \sum_{\{i,j\} \in E(R_{kl})} d_{ij} + H_k w_{kl}.$$
--   $\mathcal M_k$ is the set of first-level routes visiting $k$, $\mathcal R_{ik}$ the routes of $\mathcal R_k$ visiting $i$, and $a_{ikl}$ the number of times route $l$ visits customer $i$.
--
--   **Formulation F.** With binary $x_{kl}$ (route $l$ used), binary $y_r$ (route $r$ used) and nonnegative integers $q_{kr}$ (quantity carried by $r$ to satellite $k$, zero if $k \notin R_r$), $F$ minimises
--   $$\sum_{k \in N_S}\sum_{l \in \mathcal R_k} c_{kl} x_{kl} + \sum_{r \in \mathcal M} g_r y_r \qquad (1)$$
--   subject to
--   1. (2) every customer lies on exactly one used second-level route;
--   2. (3) at most $m_k$ routes are used at satellite $k$;
--   3. (4) at most $m^2$ second-level routes are used;
--   4. (5) $\sum_{l \in \mathcal R_k} w_{kl} x_{kl} \le B_k$;
--   5. (6) at most $m^1$ first-level routes are used;
--   6. (7) $\sum_{r \in \mathcal M_k} q_{kr} = \sum_{l \in \mathcal R_k} w_{kl} x_{kl}$;
--   7. (8) $\sum_{k \in R_r} q_{kr} \le Q_1 y_r$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Satellites are `Fin ns` and customers `Fin nc` (0-based). The triangle inequality is not imposed: no statement of the mission uses it, so the statements are stronger. Demands are read as positive, the reading the paper's constructions rely on; the second-level capacity is also required positive ($Q_2 > 0$, not printed), which excludes only instances where no second-level route can exist. The paper takes $\mathcal M$ and $\mathcal R_k$ to be all routes (with prescribed copies of each single-satellite route); here they are arbitrary finite families of routes with the properties above, a generalization. Route costs are computed along the closed walk, so the route $(0,k,0)$ costs $2d_{0k}$, as §2.2 of the paper presupposes. The binary and integrality conditions (9)–(11) are carried by the types (`Bool`, `ℕ`).
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), pp. 299–300, §2 and §2.1, formulation F (1)–(11)

import Mathlib

namespace TwoEchelonCVRP.LowerBound

/-- The vertices of the 2E-CVRP graph `G = (N, E)` of Baldacci, Mingozzi, Roberti & Wolfler Calvo,
Oper. Res. 61(2) (2013), §2, p. 299: the depot `0`, the satellites `N_S` and the customers `N_C`.
Satellite `sat k` (`k : Fin ns`) is the paper's satellite `k + 1`; customer `cust i`
(`i : Fin nc`) is the paper's customer `n_s + i + 1`. -/
inductive Vertex (ns nc : ℕ) where
  | depot : Vertex ns nc
  | sat : Fin ns → Vertex ns nc
  | cust : Fin nc → Vertex ns nc
  deriving DecidableEq

/-- An instance of the two-echelon capacitated vehicle routing problem (§2, p. 299).

* `d` is the travel cost matrix **after** the fixed costs have been folded in, as the paper does
  from p. 299 on (`U_1/2` added to `d_{0k}`, `U_2/2` added to `d_{ki}`); it is symmetric. Only its
  values on the edges of `E` are ever used.
* `q i` is the demand of customer `i`, a positive integer.
* `Q1`, `Q2` are the first- and second-level vehicle capacities, `Q2 < Q1`.
* `m1` is the number of first-level vehicles; `m k` the number of second-level vehicles at
  satellite `k`; `m2 ≤ ∑ k, m k` the global bound on second-level vehicles.
* `B k` is the capacity of satellite `k` and `H k` its handling cost per unit.

Formalization Note: the triangle inequality on `d` is not imposed (it is not used by any statement
of this mission, and does not survive the fixed-cost modification in general). Demands are read as
positive (`q_pos`), the reading the paper's constructions rely on. -/
structure Instance where
  ns : ℕ
  nc : ℕ
  d : Vertex ns nc → Vertex ns nc → ℝ
  d_symm : ∀ u v, d u v = d v u
  q : Fin nc → ℕ
  q_pos : ∀ i, 0 < q i
  Q1 : ℕ
  Q2 : ℕ
  Q2_pos : 0 < Q2
  Q2_lt_Q1 : Q2 < Q1
  m1 : ℕ
  m2 : ℕ
  m : Fin ns → ℕ
  m2_le : m2 ≤ ∑ k, m k
  B : Fin ns → ℕ
  H : Fin ns → ℝ

/-- Total customer demand `q_tot = ∑_{i ∈ N_C} q_i`. -/
def Instance.qtot (I : Instance) : ℕ := ∑ i, I.q i

/-- Cost of the closed walk `s → v₁ → ⋯ → v_p → s`: the sum of `d` over consecutive pairs.
A route `(0, k, 0)` therefore costs `2 d_{0k}`. -/
def closedWalkCost {V : Type} (d : V → V → ℝ) (s : V) (l : List V) : ℝ :=
  (List.zipWith d (s :: l) (l ++ [s])).sum

/-- The families of first-level routes `𝓜` and second-level routes `𝓡` (§2.1, pp. 299–300).

* `FR` indexes `𝓜`; route `r` visits the satellites `tour1 r` in that order (nonempty, no
  repetition), starting and ending at the depot. Copies of the same route are distinct indices.
* `SR` indexes `𝓡`; route `l` starts and ends at satellite `sat l` (`π_l`) and visits the
  customers `tour2 l` in that order (nonempty, no repetition: a simple cycle). Its load
  `w_l = ∑_{i ∈ R_l} q_i` does not exceed `Q_2`.

Formalization Note: the paper takes `𝓜` and `𝓡_k` to be all such routes (with
`⌈min{m_k Q_2, q_tot}/Q_1⌉` copies of each `(0, k, 0)`); here they are arbitrary finite families
with these properties, a generalization. -/
structure RouteSystem (I : Instance) where
  FR : Type
  [fintypeFR : Fintype FR]
  [decEqFR : DecidableEq FR]
  tour1 : FR → List (Fin I.ns)
  tour1_ne : ∀ r, tour1 r ≠ []
  tour1_nodup : ∀ r, (tour1 r).Nodup
  SR : Type
  [fintypeSR : Fintype SR]
  [decEqSR : DecidableEq SR]
  sat : SR → Fin I.ns
  tour2 : SR → List (Fin I.nc)
  tour2_ne : ∀ l, tour2 l ≠ []
  tour2_nodup : ∀ l, (tour2 l).Nodup
  cap2 : ∀ l, ∑ i ∈ (tour2 l).toFinset, I.q i ≤ I.Q2

attribute [instance] RouteSystem.fintypeFR RouteSystem.decEqFR
  RouteSystem.fintypeSR RouteSystem.decEqSR

variable {I : Instance}

/-- `R_r`: the satellites visited by first-level route `r`. -/
def RouteSystem.Rsat (RS : RouteSystem I) (r : RS.FR) : Finset (Fin I.ns) := (RS.tour1 r).toFinset

/-- `g_r`: the cost of first-level route `r`, the closed walk from the depot through its
satellites. -/
def RouteSystem.g (RS : RouteSystem I) (r : RS.FR) : ℝ :=
  closedWalkCost I.d Vertex.depot ((RS.tour1 r).map Vertex.sat)

/-- `R_{kl}`: the customers visited by second-level route `l`. -/
def RouteSystem.Rcust (RS : RouteSystem I) (l : RS.SR) : Finset (Fin I.nc) := (RS.tour2 l).toFinset

/-- `a_{ikl}`: the number of times route `l` visits customer `i` (0 or 1 here). -/
def RouteSystem.a (RS : RouteSystem I) (i : Fin I.nc) (l : RS.SR) : ℕ := (RS.tour2 l).count i

/-- `w_{kl} = ∑_{i ∈ R_{kl}} q_i`: the load of second-level route `l`. -/
def RouteSystem.w (RS : RouteSystem I) (l : RS.SR) : ℕ := ∑ i ∈ RS.Rcust l, I.q i

/-- `c_{kl}`: travel cost of the closed walk from `π_l` plus the handling cost `H_k w_{kl}`. -/
def RouteSystem.c (RS : RouteSystem I) (l : RS.SR) : ℝ :=
  closedWalkCost I.d (Vertex.sat (RS.sat l)) ((RS.tour2 l).map Vertex.cust)
    + I.H (RS.sat l) * (RS.w l : ℝ)

/-- A choice of the variables of formulation F: `x l = x_{kl}` (route `l` of satellite
`k = π_l` is used), `y r = y_r`, and `qd r k = q_{kr}` (quantity delivered by first-level route `r`
to satellite `k`). The binary and integrality conditions (9)–(11) are carried by the types. -/
structure SolF (RS : RouteSystem I) where
  x : RS.SR → Bool
  y : RS.FR → Bool
  qd : RS.FR → Fin I.ns → ℕ

/-- Feasibility for formulation F (§2.1, p. 300), constraints (2)–(8) plus the convention
`q_{kr} = 0` for `k ∉ R_r`. -/
def IsFeasibleF (RS : RouteSystem I) (s : SolF RS) : Prop :=
  -- (2): every customer is served by exactly one used second-level route
  (∀ i, ∑ l ∈ Finset.univ.filter (fun l => i ∈ RS.tour2 l), (s.x l).toNat = 1) ∧
  -- (3): at most `m_k` routes at satellite `k`
  (∀ k, ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (s.x l).toNat ≤ I.m k) ∧
  -- (4): at most `m^2` second-level routes in total
  (∑ l, (s.x l).toNat ≤ I.m2) ∧
  -- (5): satellite capacity
  (∀ k, ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), RS.w l * (s.x l).toNat ≤ I.B k) ∧
  -- (6): at most `m^1` first-level routes
  (∑ r, (s.y r).toNat ≤ I.m1) ∧
  -- (7): flow balance at satellite `k`
  (∀ k, ∑ r ∈ Finset.univ.filter (fun r => k ∈ RS.Rsat r), s.qd r k
      = ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), RS.w l * (s.x l).toNat) ∧
  -- (8): first-level capacity
  (∀ r, ∑ k ∈ RS.Rsat r, s.qd r k ≤ I.Q1 * (s.y r).toNat) ∧
  -- convention: `q_{kr} = 0` for `k ∉ R_r`
  (∀ r k, k ∉ RS.Rsat r → s.qd r k = 0)

/-- The objective (1) of formulation F. -/
def costF (RS : RouteSystem I) (s : SolF RS) : ℝ :=
  ∑ l, RS.c l * ((s.x l).toNat : ℝ) + ∑ r, RS.g r * ((s.y r).toNat : ℝ)

end TwoEchelonCVRP.LowerBound


