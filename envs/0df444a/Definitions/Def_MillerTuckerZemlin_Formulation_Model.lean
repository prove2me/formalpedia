-- Prove2me | Definitions.Def_MillerTuckerZemlin_Formulation_Model
-- name    : MillerTuckerZemlin_Formulation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:09:42.147087+00:00
-- url     : https://prove2.me/theorems/963906c4-aa25-4887-9a55-c7bbcf524609
-- title:
--   Problems (1) and (2), pp. 326–327: itineraries from base city 0 with at most p cities per tour, their arcs and length; the feasible set and objective of the MTZ integer program
-- statement:
--   This file sets up the two problems of Miller, Tucker and Zemlin (1960).
--
--   **Cities.** There are $n$ cities $1,\dots,n$ and a **base city** $0$; the city set is $\{0,1,\dots,n\}$.
--
--   **Problem (1): itineraries.** A salesman leaves city $0$, visits each of the cities $1,\dots,n$ exactly once, and returns to $0$, possibly several times. A **tour** is a succession of visits to cities without stopping at city $0$. An **itinerary** is the list $I = (T_1,\dots,T_t)$ of its tours in the order travelled, each tour $T = (c_1,\dots,c_k)$ being the list of cities visited between two stops at $0$; the number of returns to $0$ is $t$. The itinerary is **legitimate with at most $p$ cities per tour** when
--
--   1. every tour is nonempty, does not contain $0$, and has at most $p$ cities;
--   2. no city occurs twice in the concatenation $T_1T_2\cdots T_t$;
--   3. every city $c\in\{1,\dots,n\}$ occurs in some tour.
--
--   Tour $T=(c_1,\dots,c_k)$ travels the **arcs** $(0,c_1),(c_1,c_2),\dots,(c_{k-1},c_k),(c_k,0)$. For an itinerary $I$ let $a_{ij}(I)$ be the number of times $I$ travels the arc $(i,j)$, and, for distances $d_{ij}\in\mathbb R$, let the **length** of $I$ be $\sum d_{ij}$ over all arcs travelled, with multiplicity.
--
--   **Problem (2): the integer program.** For non-negative integers $x_{ij}$ ($0\le i\ne j\le n$) and real numbers $u_1,\dots,u_n$, the pair $(x,u)$ is **feasible** when
--
--   $$
--   \sum_{\substack{i=0\\ i\ne j}}^{n} x_{ij}=1\ (j=1,\dots,n),\qquad \sum_{\substack{j=0\\ j\ne i}}^{n} x_{ij}=1\ (i=1,\dots,n),\qquad u_i-u_j+p\,x_{ij}\le p-1\ (1\le i\ne j\le n).
--   $$
--
--   The objective of (2) is the linear form $\sum\sum_{0\le i\ne j\le n} d_{ij}x_{ij}$.
--
--   Finally, for a legitimate itinerary, the **tour position** of a city $i\ne 0$ is $j$ when $i$ is the $j$-th city visited in the tour that contains it; this is the labelling $u_i$ of the paper's converse.
--
--   These objects are shared by every statement of the mission: the goal says that the feasible $x$ of (2) are exactly the arc counts $a(I)$ of the legitimate itineraries of (1), and that the two objectives agree.
--
--   **Formalization Note** Cities are `Fin (n + 1)` with `0` the base city. An itinerary is a `List (List (Fin (n + 1)))`; the number of returns to $0$ is its length. Arc counts are counts, not $0/1$ indicators, so that $x_{ij}\in\{0,1\}$ is a theorem about (2) and not a feature of the encoding. Problem (2) has no variables $x_{ii}$; a matrix $x$ indexed by all pairs encodes their absence by the clause $x_{ii}=0$ of `Feasible`. The vector $u$ is indexed by `Fin (n + 1)`; $u_0$ is not a variable of (2) and appears in no constraint. The constants $p-1$ and $p\,x_{ij}$ are computed in $\mathbb R$. `tourPosition` is $0$ at the base city and at a city lying on no tour. Fixed $t$ (the extra relation $\sum_{i=1}^n x_{i0}=t$) is not a separate definition: the goal identifies $\sum_{i=1}^n x_{i0}$ with the number of tours.
-- source:
--   Miller, Tucker, Zemlin, Integer Programming Formulation of Traveling Salesman Problems, J. ACM 7(4) (1960), pp. 326–328: problem (1) (p. 326), problem (2) (p. 327), the labelling u_i = j of the converse (p. 328). DOI 10.1145/321043.321046

import Mathlib

namespace MillerTuckerZemlin.Formulation

/-- An itinerary for problem (1) of Miller, Tucker, Zemlin, *Integer Programming Formulation of
Traveling Salesman Problems*, J. ACM 7(4) (1960), p. 326: the list of tours in the order they are
travelled, each tour being the list of cities visited between two stops at the base city `0`.
Cities are `Fin (n + 1)`: `0` is the base city and `1, …, n` are the paper's cities. -/
abbrev Itinerary (n : ℕ) := List (List (Fin (n + 1)))

/-- A legitimate itinerary of problem (1) (p. 326) with at most `p` cities per tour: every tour is
nonempty, avoids the base city `0` and visits at most `p` cities; no city is visited twice; and every
city `c ≠ 0` is visited. The number of returns to `0` is `I.length`. -/
def IsItinerary (n p : ℕ) (I : Itinerary n) : Prop :=
  (∀ T ∈ I, T ≠ [] ∧ (0 : Fin (n + 1)) ∉ T ∧ T.length ≤ p) ∧
  I.flatten.Nodup ∧
  ∀ c : Fin (n + 1), c ≠ 0 → c ∈ I.flatten

/-- The arcs travelled on one tour `T = [c₁, …, c_k]`: the consecutive pairs of the closed walk
`0, c₁, …, c_k, 0`. -/
def tourArcs {n : ℕ} (T : List (Fin (n + 1))) : List (Fin (n + 1) × Fin (n + 1)) :=
  (0 :: T).zip (T ++ [0])

/-- All arcs travelled along an itinerary, with multiplicity. -/
def arcs {n : ℕ} (I : Itinerary n) : List (Fin (n + 1) × Fin (n + 1)) :=
  I.flatMap tourArcs

/-- The number of times the itinerary travels directly from city `i` to city `j`
(the paper's correspondence: "the salesman proceeds from city i to city j if and only if
x_ij = 1", p. 327). -/
def arcCount {n : ℕ} (I : Itinerary n) (i j : Fin (n + 1)) : ℕ :=
  (arcs I).count (i, j)

/-- The total distance travelled along an itinerary, for the distances `d i j` of p. 326. -/
def itineraryLength {n : ℕ} (d : Fin (n + 1) → Fin (n + 1) → ℝ) (I : Itinerary n) : ℝ :=
  ((arcs I).map (fun a => d a.1 a.2)).sum

/-- The feasible set of problem (2) (p. 327): `x i j` (non-negative integers) and `u i` (arbitrary
reals) with
* `∑_{i = 0, i ≠ j}^n x_ij = 1` for `j = 1, …, n`,
* `∑_{j = 0, j ≠ i}^n x_ij = 1` for `i = 1, …, n`,
* `u_i − u_j + p x_ij ≤ p − 1` for `1 ≤ i ≠ j ≤ n`.
Problem (2) has no variables `x_ii`; the clause `x i i = 0` encodes their absence. `u 0` is not a
variable of (2) and is unconstrained. -/
def Feasible (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, x i i = 0) ∧
  (∀ j : Fin (n + 1), j ≠ 0 → ∑ i ∈ Finset.univ.filter (· ≠ j), x i j = 1) ∧
  (∀ i : Fin (n + 1), i ≠ 0 → ∑ j ∈ Finset.univ.filter (· ≠ i), x i j = 1) ∧
  (∀ i j : Fin (n + 1), i ≠ 0 → j ≠ 0 → i ≠ j →
    u i - u j + (p : ℝ) * (x i j : ℝ) ≤ (p : ℝ) - 1)

/-- The objective of problem (2) (p. 327): `∑∑_{0 ≤ i ≠ j ≤ n} d_ij x_ij`. -/
def objective {n : ℕ} (d : Fin (n + 1) → Fin (n + 1) → ℝ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (· ≠ i), d i j * (x i j : ℝ)

/-- The labelling of the converse (p. 328): `u_i = j` if city `i` is the `j`-th city visited in the
tour which includes city `i` (1-based); `0` for the base city and for a city on no tour. -/
def tourPosition {n : ℕ} (I : Itinerary n) (i : Fin (n + 1)) : ℕ :=
  if i = 0 then 0 else
    match I.find? (fun T => decide (i ∈ T)) with
    | some T => T.idxOf i + 1
    | none => 0

end MillerTuckerZemlin.Formulation


