-- Prove2me | Definitions.Def_BellmanRouting_PolicySpace_Routing
-- name    : BellmanRouting_PolicySpace_Routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:08:39.965542+00:00
-- url     : https://prove2.me/theorems/0847c0a2-693f-4a34-8364-f7b3415c32ad
-- title:
--   The routing problem: routes to city N, their times, minimal times (3.1), the system (3.2), and the approximations (5.1)–(5.2) and (7.1)
-- statement:
--   There are $N = n + 1$ cities, every two linked by a direct road, and city $N$ is the destination. For cities $i, j$ the number $t_{ij}$ is the time required to travel from $i$ to $j$; the matrix $T = (t_{ij})$ need not be symmetric.
--
--   1. **Routes.** A route from $i$ to $N$ is a sequence of cities $i = c_0, c_1, \dots, c_m = N$ in which consecutive cities are distinct. Cities may repeat. Its stops are $c_1, \dots, c_{m-1}$, so a route with at most $k$ stops uses at most $k+1$ roads. When $i = N$, the trivial route with $m = 0$ is allowed. The time of a route is
--   $$\tau(c) = \sum_{r=0}^{m-1} t_{c_r c_{r+1}},$$
--   and the trivial route has time $0$.
--   2. **Minimal time (3.1).** A real number $v$ is *the minimal time from $i$ to $N$* if some route from $i$ to $N$ has time $v$ and every route from $i$ to $N$ has time at least $v$. Likewise, $v$ is *the minimal time from $i$ with at most $k$ stops* if it is attained by, and is a lower bound for, the routes with at most $k+1$ roads.
--   3. **The system (3.2).** A vector $F = (F_1, \dots, F_N)$ solves (3.2) if
--   $$F_i = \min_{j \ne i}\,[t_{ij} + F_j] \quad (i = 1, \dots, N-1), \qquad F_N = 0 .$$
--   The minimum runs over all $j \ne i$, the destination included.
--   4. **Approximation in policy space (§5).** The sequence $f^{(k)}$ starts from the direct-route policy (5.2), $f_i^{(0)} = t_{iN}$ for $i \ne N$ and $f_N^{(0)} = 0$, and continues by (5.1):
--   $$f_i^{(k+1)} = \min_{j \ne i}\,[t_{ij} + f_j^{(k)}] \quad (i \ne N), \qquad f_N^{(k+1)} = 0 .$$
--   5. **Monotone increasing scheme (§7, (7.1)).** The sequence $\underline f^{(k)}$ starts from $\underline f_i^{(0)} = \min_{j \ne i} t_{ij}$ for $i \ne N$ and $\underline f_N^{(0)} = 0$, and continues by the same step as (5.1).
--
--   These are the objects shared by every statement of the mission. The minimal time is defined directly from routes, independently of (3.2) and of either iteration.
--
--   **Formalization Note** Cities are `Fin (n + 1)`, and the paper's city $N$ is `Fin.last n`. A route from `i` is the list `[c₁, …, c_m]` of the cities after `i` (`IsRoute`), and `routeTime` sums the road times. Minimal times are attained minima (`IsMinTime`, `IsMinTimeWithin`), not infima, so they assert existence. `minStep t F` is the right-hand side of (3.2)/(5.1), a `Finset.inf'` over $j \ne i$; the lemma `erase_nonempty` only records that this index set contains the destination. The paper prints (5.2) as $f_i^{(0)} = t_{iN}$ for $i = 1, \dots, N$, which would set $f_N^{(0)} = t_{NN}$; `approx` uses $f_N^{(0)} = 0$, the value its own justification of (5.4) requires (see the (5.4) item). (7.1) prints "$i = 1, 2, \cdots, N = 1$" for $N - 1$.
-- source:
--   Bellman, On a routing problem, Quart. Appl. Math. 16 (1958), p. 87, Section 2 and Section 3, Eqs. (3.1)–(3.2); p. 88, Eq. (5.1); p. 89, Eq. (5.2) and Section 7, Eq. (7.1)

import Mathlib

namespace BellmanRouting.PolicySpace

/-! The routing problem of Bellman (1958), Sections 2, 3, 5 and 7.

There are `N = n + 1` cities, `Fin (n + 1)`; the paper's city `N` (the destination) is
`Fin.last n`. The travel time from `i` to `j` is `t i j`. -/

/-- `IsRoute i l`: the list `l = [c₁, …, c_m]` lists the cities visited after the start `i`,
so that `i = c₀, c₁, …, c_m` is a route from `i` to the destination `Fin.last n`:
consecutive cities are distinct and the last city is the destination. The empty list is
the trivial route, allowed only when `i` is the destination. Cities may repeat (walks). -/
def IsRoute {n : ℕ} : Fin (n + 1) → List (Fin (n + 1)) → Prop
  | i, [] => i = Fin.last n
  | i, j :: l => i ≠ j ∧ IsRoute j l

/-- The total travel time `t_{c₀c₁} + t_{c₁c₂} + ⋯ + t_{c_{m−1}c_m}` of the route
`i = c₀, c₁, …, c_m` with `l = [c₁, …, c_m]`. The trivial route has time `0`. -/
def routeTime {n : ℕ} (t : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 1) → List (Fin (n + 1)) → ℝ
  | _, [] => 0
  | i, j :: l => t i j + routeTime t j l

/-- `IsMinTime t i v` (3.1): `v` is the minimal time to travel from `i` to the destination,
an attained minimum: some route from `i` has time `v`, and every route from `i` has time
at least `v`. -/
def IsMinTime {n : ℕ} (t : Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin (n + 1)) (v : ℝ) : Prop :=
  (∃ l, IsRoute i l ∧ routeTime t i l = v) ∧ ∀ l, IsRoute i l → v ≤ routeTime t i l

/-- `IsMinTimeWithin t k i v`: `v` is the minimal time over routes from `i` to the destination
with at most `k` stops, i.e. at most `k + 1` roads (`l.length ≤ k + 1`): attained by such a
route and at most the time of every such route. -/
def IsMinTimeWithin {n : ℕ} (t : Fin (n + 1) → Fin (n + 1) → ℝ) (k : ℕ) (i : Fin (n + 1))
    (v : ℝ) : Prop :=
  (∃ l, IsRoute i l ∧ l.length ≤ k + 1 ∧ routeTime t i l = v) ∧
    ∀ l, IsRoute i l → l.length ≤ k + 1 → v ≤ routeTime t i l

/-- For a city `i` other than the destination, the index set `{j : j ≠ i}` of the minimum
in (3.2) is nonempty: it contains the destination. -/
theorem erase_nonempty {n : ℕ} {i : Fin (n + 1)} (h : i ≠ Fin.last n) :
    (Finset.univ.erase i).Nonempty :=
  ⟨Fin.last n, Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ _⟩⟩

/-- The right-hand side of (3.2) and (5.1): `0` at the destination, and
`Min_{j ≠ i} [t_ij + F_j]` at every other city `i` (the minimum over all `j ≠ i`,
the destination included). -/
noncomputable def minStep {n : ℕ} (t : Fin (n + 1) → Fin (n + 1) → ℝ) (F : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  if h : i = Fin.last n then 0
  else (Finset.univ.erase i).inf'
    (erase_nonempty h) (fun j => t i j + F j)

/-- `F` solves the system (3.2): `F_N = 0` and `F_i = Min_{j ≠ i} [t_ij + F_j]` for `i ≠ N`. -/
def IsRoutingSolution {n : ℕ} (t : Fin (n + 1) → Fin (n + 1) → ℝ) (F : Fin (n + 1) → ℝ) :
    Prop :=
  ∀ i, F i = minStep t F i

/-- The successive approximations of Section 5: `f^(0)` is the direct-route policy (5.2),
`f_i^(0) = t_iN` for `i ≠ N` and `f_N^(0) = 0` (the paper prints `t_NN` at `i = N`; see the
item's note), and `f^(k+1)` is given by (5.1). -/
noncomputable def approx {n : ℕ} (t : Fin (n + 1) → Fin (n + 1) → ℝ) : ℕ → Fin (n + 1) → ℝ
  | 0 => fun i => if i = Fin.last n then 0 else t i (Fin.last n)
  | k + 1 => minStep t (approx t k)

/-- The successive approximations of Section 7, (7.1): `f_i^(0) = Min_{j ≠ i} t_ij` for
`i ≠ N`, `f_N^(0) = 0`, and `f^(k+1)` given by the same step as (5.1). -/
noncomputable def approxUp {n : ℕ} (t : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ℕ → Fin (n + 1) → ℝ
  | 0 => fun i =>
      if h : i = Fin.last n then 0
      else (Finset.univ.erase i).inf'
        (erase_nonempty h) (fun j => t i j)
  | k + 1 => minStep t (approxUp t k)

end BellmanRouting.PolicySpace


