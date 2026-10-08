-- Prove2me | Definitions.Def_DialARideBC_Valid_Model
-- name    : DialARideBC_Valid_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:03.072442+00:00
-- url     : https://prove2.me/theorems/53abe6e8-0415-41f8-a7ed-703c09194abd
-- title:
--   §3–§4, pp. 574–576 — DARP instances, route-based feasible solutions, arc variables x^k_ij, x_ij, x(S), δ⁺, δ⁻, π(S), σ(S)
-- statement:
--   **The dial-a-ride problem (DARP).** Let $n$ be the number of users. The DARP is defined on the complete directed graph on the node set
--   $$N = P \cup D \cup \{0, 2n+1\},\qquad P = \{1,\dots,n\},\qquad D = \{n+1,\dots,2n\}.$$
--   Nodes $0$ and $2n+1$ are the origin and destination depots; user $i \in P$ has pick-up node $i$ and drop-off node $n+i$.
--
--   An **instance** with vehicle set $K$ consists of a load $q_i$, a service duration $d_i$ and a time window $[e_i, l_i]$ for every node $i$, a travel time $t_{ij}$ for every arc $(i,j)$, a capacity $Q_k$ and a maximal route duration $T_k$ for every vehicle $k$, and a maximal user ride time $L$, subject to the standing conditions of §3:
--   $$q_0 = q_{2n+1} = 0,\qquad q_i = -q_{n+i}\ (i \in P),\qquad d_i \ge 0\ (i\in N),\qquad d_0 = d_{2n+1} = 0.$$
--
--   A **feasible solution** assigns to every vehicle $k$ a route $0 \to v_1 \to \dots \to v_r \to 2n+1$ through distinct nodes of $P \cup D$, together with service start times $B^k_i$ and loads $Q^k_i$, such that
--
--   1. every node of $P \cup D$ is visited by exactly one vehicle (constraints (2), (5));
--   2. user $i$'s nodes $i$ and $n+i$ are on the same route (3), and $i$ is visited before $n+i$ (precedence);
--   3. on every arc $(i,j)$ of a route of vehicle $k$: $B^k_j \ge B^k_i + d_i + t_{ij}$ (7) and $Q^k_j \ge Q^k_i + q_j$ (8);
--   4. for every user $i$ on vehicle $k$, the ride time $L^k_i = B^k_{n+i} - (B^k_i + d_i)$ satisfies $t_{i,n+i} \le L^k_i \le L$ ((9), (12));
--   5. $B^k_{2n+1} - B^k_0 \le T_k$ (10);
--   6. at every node $i$ of the route of $k$: $e_i \le B^k_i \le l_i$ (11) and $\max\{0, q_i\} \le Q^k_i \le \min\{Q_k, Q_k + q_i\}$ (13).
--
--   The **arc variables** are $x^k_{ij} = 1$ if $(i,j)$ is an arc of the route of vehicle $k$ and $0$ otherwise, and the total flow is $x_{ij} = \sum_{k\in K} x^k_{ij}$. For a function $x$ on arcs and a node set $S$, write $\bar S = N \setminus S$ and
--   $$x(S) = \sum_{i,j \in S} x_{ij},\qquad x(\delta^+(S)) = \sum_{i \in S}\sum_{j\in\bar S} x_{ij},\qquad x(\delta^-(S)) = \sum_{i \in \bar S}\sum_{j\in S} x_{ij},$$
--   $$\pi(S) = \{i \in P \mid n+i \in S\},\qquad \sigma(S) = \{n+i \in D \mid i \in S\}.$$
--   The file also records the predecessor inequality (30) for a set $S$,
--   $$x(S) + \sum_{i\in S}\sum_{j\in \bar S\cap\pi(S)} x_{ij} + \sum_{i\in S\cap\pi(S)}\sum_{j\in\bar S\setminus\pi(S)} x_{ij} \le |S| - 1,$$
--   and the setting of §4.5: sets $U_1,\dots,U_m \subseteq N$, mutually disjoint, and users $i_1,\dots,i_m \in P$ with $0, 2n+1 \notin U_l$ and $i_l, n+i_{l+1} \in U_l$ for $l = 1,\dots,m$, where $i_{m+1} = i_1$.
--
--   These objects are the common language of every valid inequality of the paper: "valid for the DARP" means satisfied by the aggregated arc variables $x_{ij}$ of every feasible solution.
--
--   **Formalization Note.** Nodes are natural numbers, so $n+i$ and $2n+1$ appear literally. Feasible solutions are *route-based*: the paper defines the DARP in words (vehicle routes from $0$ to $2n+1$ satisfying capacity, duration, time-window, pairing, precedence and ride-time constraints) and formulates it as the program (1)–(14); read literally, (1)–(14) admits closed cycles of zero duration when $d_i + t_{ij} = 0$ around a cycle, and imposes (11)–(13) also on nodes a vehicle does not visit. The route encoding excludes cycles, imposes (7), (8) on the arcs actually travelled (which is what the products with $x^k_{ij}$ in (7)–(8) say when $x^k_{ij} = 1$), and (11), (13) on visited nodes; (4), (6) and (14) hold by construction. Precedence is a separate condition because with zero travel and service times the nonnegativity of $L^k_i$ alone does not order the visits. The routing cost $c^k_{ij}$ enters only the objective (1), which no statement uses, and is omitted. A vehicle may drive the empty route $0 \to 2n+1$.
-- source:
--   Cordeau, A Branch-and-Cut Algorithm for the Dial-a-Ride Problem, Oper. Res. 54(3) (2006), pp. 574–577: §3 Formulation, model (1)–(14) (p. 575); notation of §4 (p. 575); π(S), σ(S) and (30) in §4.2 (p. 576); setting of §4.5 (p. 577)

import Mathlib

namespace DialARideBC.Valid

/-- The node set `N = {0, 1, …, 2n + 1}`: origin depot `0`, pick-up nodes `1, …, n`,
drop-off nodes `n + 1, …, 2n`, destination depot `2n + 1`. -/
def N (n : ℕ) : Finset ℕ := Finset.range (2 * n + 2)

/-- Pick-up nodes `P = {1, …, n}`. -/
def P (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- Drop-off nodes `D = {n + 1, …, 2n}`. -/
def D (n : ℕ) : Finset ℕ := Finset.Icc (n + 1) (2 * n)

/-- `P ∪ D = {1, …, 2n}`. -/
def PD (n : ℕ) : Finset ℕ := Finset.Icc 1 (2 * n)

/-- A DARP instance with `n` users and vehicle set `K` (§3, p. 574): loads `q`, service
durations `d`, time windows `[e_i, l_i]`, travel times `t`, vehicle capacities `Q_k`
(`Qcap`), maximal route durations `T_k` (`Tmax`) and maximal ride time `L`, with the
standing conditions of §3. -/
structure Instance (n : ℕ) (K : Type) where
  q : ℕ → ℝ
  d : ℕ → ℝ
  e : ℕ → ℝ
  l : ℕ → ℝ
  t : ℕ → ℕ → ℝ
  Qcap : K → ℝ
  Tmax : K → ℝ
  L : ℝ
  q_zero : q 0 = 0
  q_end : q (2 * n + 1) = 0
  q_pair : ∀ i ∈ P n, q i = -q (n + i)
  d_nonneg : ∀ i ∈ N n, 0 ≤ d i
  d_zero : d 0 = 0
  d_end : d (2 * n + 1) = 0

/-- The full route `0 → v₁ → ⋯ → v_r → 2n + 1` of a vehicle whose list of visited
nodes of `P ∪ D` is `r`. -/
def fullPath (n : ℕ) (r : List ℕ) : List ℕ := 0 :: (r ++ [2 * n + 1])

/-- The arcs `(u, v)` travelled along a list of nodes: its consecutive pairs. -/
def arcs (w : List ℕ) : List (ℕ × ℕ) := w.zip w.tail

/-- A feasible DARP solution (route-based reading of model (1)–(14), p. 575). Each vehicle
`k` drives one route `0 → route k → 2n + 1` through distinct nodes of `P ∪ D`; `B k i` is
the time `B^k_i` at which `k` begins service at `i`, and `Qv k i` the load `Q^k_i` of `k`
after visiting `i`. -/
structure Solution {n : ℕ} {K : Type} (I : Instance n K) where
  route : K → List ℕ
  B : K → ℕ → ℝ
  Qv : K → ℕ → ℝ
  /-- a route visits each node at most once -/
  nodup : ∀ k, (route k).Nodup
  /-- routes visit only pick-up and drop-off nodes between the depots -/
  sub : ∀ k, ∀ v ∈ route k, v ∈ PD n
  /-- (2) with (5): every node of `P ∪ D` is visited by exactly one vehicle -/
  served : ∀ v ∈ PD n, ∃! k, v ∈ route k
  /-- (3): the origin and destination of a user are visited by the same vehicle -/
  pairing : ∀ i ∈ P n, ∀ k, i ∈ route k ↔ n + i ∈ route k
  /-- precedence: node `i` is visited before node `n + i` -/
  precedence : ∀ i ∈ P n, ∀ k, i ∈ route k →
    (route k).idxOf i < (route k).idxOf (n + i)
  /-- (7) on every arc of the route -/
  time : ∀ k, ∀ a ∈ arcs (fullPath n (route k)),
    B k a.1 + I.d a.1 + I.t a.1 a.2 ≤ B k a.2
  /-- (8) on every arc of the route -/
  load : ∀ k, ∀ a ∈ arcs (fullPath n (route k)),
    Qv k a.1 + I.q a.2 ≤ Qv k a.2
  /-- (9) and (12): the ride time `L^k_i = B^k_{n+i} − (B^k_i + d_i)` lies in `[t_{i,n+i}, L]` -/
  ride : ∀ i ∈ P n, ∀ k, i ∈ route k →
    I.t i (n + i) ≤ B k (n + i) - (B k i + I.d i) ∧ B k (n + i) - (B k i + I.d i) ≤ I.L
  /-- (10): route duration -/
  duration : ∀ k, B k (2 * n + 1) - B k 0 ≤ I.Tmax k
  /-- (11): time windows at the nodes the vehicle visits -/
  window : ∀ k, ∀ v ∈ fullPath n (route k), I.e v ≤ B k v ∧ B k v ≤ I.l v
  /-- (13): capacity at the nodes the vehicle visits -/
  capacity : ∀ k, ∀ v ∈ fullPath n (route k),
    max 0 (I.q v) ≤ Qv k v ∧ Qv k v ≤ min (I.Qcap k) (I.Qcap k + I.q v)

/-- `x^k_ij = 1` if vehicle `k` travels from node `i` to node `j`, and `0` otherwise. -/
def Solution.xk {n : ℕ} {K : Type} {I : Instance n K} (s : Solution I) (k : K) (i j : ℕ) : ℝ :=
  if (i, j) ∈ arcs (fullPath n (s.route k)) then 1 else 0

/-- The total flow `x_ij = Σ_{k ∈ K} x^k_ij` on arc `(i, j)`. -/
def Solution.x {n : ℕ} {K : Type} [Fintype K] {I : Instance n K} (s : Solution I)
    (i j : ℕ) : ℝ :=
  ∑ k, s.xk k i j

/-- `x(S) = Σ_{i, j ∈ S} x_ij`. -/
def xset (x : ℕ → ℕ → ℝ) (S : Finset ℕ) : ℝ := ∑ i ∈ S, ∑ j ∈ S, x i j

/-- `x(δ⁺(S)) = Σ_{i ∈ S, j ∈ S̄} x_ij` with `S̄ = N \ S`. -/
def xOut (n : ℕ) (x : ℕ → ℕ → ℝ) (S : Finset ℕ) : ℝ := ∑ i ∈ S, ∑ j ∈ N n \ S, x i j

/-- `x(δ⁻(S)) = Σ_{i ∈ S̄, j ∈ S} x_ij` with `S̄ = N \ S`. -/
def xIn (n : ℕ) (x : ℕ → ℕ → ℝ) (S : Finset ℕ) : ℝ := ∑ i ∈ N n \ S, ∑ j ∈ S, x i j

/-- Predecessors `π(S) = {i ∈ P | n + i ∈ S}`. -/
def pred (n : ℕ) (S : Finset ℕ) : Finset ℕ := (P n).filter (fun i => n + i ∈ S)

/-- Successors `σ(S) = {n + i ∈ D | i ∈ S}`. -/
def succ (n : ℕ) (S : Finset ℕ) : Finset ℕ := (P n ∩ S).image (fun i => n + i)

/-- The predecessor inequality (30), p. 576, for the set `S`:
`x(S) + Σ_{i ∈ S} Σ_{j ∈ S̄ ∩ π(S)} x_ij + Σ_{i ∈ S ∩ π(S)} Σ_{j ∈ S̄ \ π(S)} x_ij ≤ |S| − 1`. -/
def predIneq (n : ℕ) (x : ℕ → ℕ → ℝ) (S : Finset ℕ) : Prop :=
  xset x S + ∑ i ∈ S, ∑ j ∈ (N n \ S) ∩ pred n S, x i j
    + ∑ i ∈ S ∩ pred n S, ∑ j ∈ (N n \ S) \ pred n S, x i j ≤ (S.card : ℝ) - 1

/-- The setting of §4.5, p. 577: `U_1, …, U_m ⊆ N` mutually disjoint, users
`i_1, …, i_m ∈ P`, `0, 2n + 1 ∉ U_l` and `i_l, n + i_{l+1} ∈ U_l` for `l = 1, …, m`, where
`i_{m+1} = i_1`. -/
def IsGOCFamily (n m : ℕ) (i : ℕ → ℕ) (U : ℕ → Finset ℕ) : Prop :=
  (∀ l ∈ Finset.Icc 1 m,
    U l ⊆ N n ∧ 0 ∉ U l ∧ 2 * n + 1 ∉ U l ∧ i l ∈ P n ∧ i l ∈ U l ∧
      n + i (if l = m then 1 else l + 1) ∈ U l) ∧
  Set.PairwiseDisjoint (↑(Finset.Icc 1 m) : Set ℕ) U

end DialARideBC.Valid


