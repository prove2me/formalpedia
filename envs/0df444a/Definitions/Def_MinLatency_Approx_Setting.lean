-- Prove2me | Definitions.Def_MinLatency_Approx_Setting
-- name    : MinLatency_Approx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:37.295108+00:00
-- url     : https://prove2.me/theorems/e26097ed-e333-4455-8c80-3f69e16de59d
-- title:
--   §1 and §3.2, pp. 1–7 — metric instances, walk latency, rooted tours, the prize-collecting cost, (α, β)-TSP-approximators and the round-trip algorithm
-- statement:
--   This file fixes the objects of the minimum latency problem (MLT) and of the approximation algorithm of §3.2 of Blum et al.
--
--   **Instances.** A finite set $V$ of points, a starting point $p\in V$ and a distance function $d:V\times V\to\mathbb R$. The predicate `IsMetric d` says that $d$ is a metric: $d(u,v)=d(v,u)$, $d(u,u)=0$, $d(u,v)>0$ for $u\neq v$, and $d(u,w)\le d(u,v)+d(v,w)$.
--
--   **Walks and latency.** A walk is a finite sequence of points $W=(w_0,w_1,\dots,w_m)$; its length is $\sum_{i<m} d(w_i,w_{i+1})$. The latency of a point $v$ in $W$ is the length of $W$ up to the **first** occurrence of $v$, and the total latency of $W$ is the sum of the latencies of all points of $V$. A covering walk from $p$ starts at $p$ and visits every point; it may revisit points.
--
--   **Tours.** A tour rooted at $p$ is a sequence of distinct points starting at $p$, closed by the return leg to $p$; its closed length is the walk length plus the distance from its last point back to $p$. For a list $T$, $\mathrm{missed}(T)$ is the number of points of $V$ not in $T$.
--
--   **Prize-collecting cost (p. 6).** For a penalty vector $\pi:V\to\mathbb R$, the cost of a tour $T$ is its closed length plus $\sum_{v\notin T}\pi(v)$. An oracle $O$, mapping penalty vectors to lists, is *admissible* when for every $\pi\ge 0$ the list $O(\pi)$ is a tour rooted at $p$ whose cost is at most twice the cost of every tour rooted at $p$.
--
--   **$(\alpha,\beta)$-TSP-approximators (Definition and Comment, p. 6).** A map $A$ from bounds to lists is an $(\alpha,\beta)$-TSP-approximator when, for every $L>0$ and every $k\in\mathbb N$: if some tour rooted at $p$ has closed length at most $L$ and misses at most $k$ points, then $A(L)$ is a tour rooted at $p$ of closed length at most $\beta L$ missing at most $\alpha k$ points.
--
--   **The algorithm (proofs of Corollary 4 and Lemma 5, pp. 6–7).**
--   1. The penalty for budget $L$ and miss count $k$ is $P_k(L)=2L/k$ for $k\ge 1$ and $P_0(L)=4L$.
--   2. The approximator $\mathrm{cor4}(L)$ calls the oracle with the constant penalty $P_k(L)$ for $k=0,1,\dots,|V|-1$, keeps the returned lists of closed length at most $6L$, and returns one that visits the most points (the first in the order of $k$); if none qualifies it returns $(p)$.
--   3. $\delta$ is the distance from $p$ to its nearest neighbour ($1$ if $p$ is the only point). Round trip $j=0,1,2,\dots$ is $T_j=A(2^{j+1}\delta)$, and the walk after round trip $J$ is the concatenation $T_0T_1\cdots T_J$. The run stops after round trip $J$ when $T_J$ visits every point and no earlier $T_j$ does.
--
--   **Bit size.** A rational $a/b$ in lowest terms has size $1+\lceil\log_2(|a|+1)\rceil+\lceil\log_2(b+1)\rceil$, and a rational distance matrix has as size the sum of the sizes of its entries.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Walks and tours are Lean lists; the latency uses `List.idxOf` (first occurrence), not `List.dedup`, which keeps last occurrences. The penalty at $k=0$ is $4L$ because the page's $2L/(\varepsilon n)$ divides by zero there, and Lean's real division would return $0$. The page's binary search over $\varepsilon$ is replaced by a scan of every miss count, keeping the page's selection rule.
-- source:
--   Blum, Chalasani, Coppersmith, Pulleyblank, Raghavan, Sudan, The Minimum Latency Problem, STOC 1994 (authors' copy, sha256 7b3a41fd…3498), PDF pp. 1–3 (problem, p-latency), p. 6 (Definition, Comment, prize-collecting problem, Lemma 3, proof of Corollary 4, proof of Lemma 5)

import Mathlib

namespace MinLatency.Approx

variable {V : Type} [Fintype V] [DecidableEq V]

/-- §1, p. 1 and §3.2, p. 6: a finite metric on the point set `V`: symmetric, zero on the diagonal,
positive between distinct points (§3.2 works in "metric spaces"), and satisfying the triangle
inequality. -/
structure IsMetric (d : V → V → ℝ) : Prop where
  symm : ∀ u v, d u v = d v u
  self : ∀ u, d u u = 0
  pos : ∀ u v, u ≠ v → 0 < d u v
  triangle : ∀ u v w, d u w ≤ d u v + d v w

/-- Length of a walk (a list of points): the sum of the distances between consecutive points.
A walk with fewer than two points has length `0`. -/
def pathLen (d : V → V → ℝ) : List V → ℝ
  | u :: v :: t => d u v + pathLen d (v :: t)
  | _ => 0

/-- Closed length of a tour: its path length plus the return leg from its last point to its first
point. The empty list has closed length `0`. -/
def tourLen (d : V → V → ℝ) : List V → ℝ
  | [] => 0
  | u :: t => pathLen d (u :: t) + d ((u :: t).getLast (List.cons_ne_nil u t)) u

/-- A tour rooted at `p` (p. 6): a list without repetitions whose first point is `p`; it is closed
by the return leg to `p` (see `tourLen`). -/
def IsRootedTour (p : V) (T : List V) : Prop := T.head? = some p ∧ T.Nodup

/-- The number of points of `V` that the list `T` does not visit. -/
def missed (T : List V) : ℕ := (Finset.univ.filter (fun v => v ∉ T)).card

/-- p. 6: the prize-collecting cost of a tour `T` under the penalty vector `π`: the total distance
travelled (closed length) plus the sum of the penalties of the points not visited. -/
def pcCost (d : V → V → ℝ) (π : V → ℝ) (T : List V) : ℝ :=
  tourLen d T + ∑ v ∈ Finset.univ.filter (fun v => v ∉ T), π v

/-- Lemma 3, p. 6, as used in the proof of Corollary 4 ("a 2-approximation algorithm for the
prize-collecting traveling salesman problem"): the oracle `O` maps every nonnegative penalty vector
to a tour rooted at `p` whose prize-collecting cost is at most twice that of every tour rooted
at `p`. -/
def PCAdmissible (d : V → V → ℝ) (p : V) (O : (V → ℝ) → List V) : Prop :=
  ∀ π : V → ℝ, (∀ v, 0 ≤ π v) →
    IsRootedTour p (O π) ∧ ∀ T, IsRootedTour p T → pcCost d π (O π) ≤ 2 * pcCost d π T

/-- The latency of `v` in the walk `W` (abstract, §1): the length of `W` up to the **first**
occurrence of `v`. -/
def firstVisit (d : V → V → ℝ) (W : List V) (v : V) : ℝ :=
  pathLen d (W.take (W.idxOf v + 1))

/-- The total latency of the walk `W`: the sum over all points of their latencies. -/
def walkLatency (d : V → V → ℝ) (W : List V) : ℝ := ∑ v, firstVisit d W v

/-- A walk starting at `p` that visits every point (§1, p. 1–3: the MLT may revisit points). -/
def IsCoveringWalk (p : V) (W : List V) : Prop := W.head? = some p ∧ ∀ v, v ∈ W

/-- Definition and Comment, p. 6, in the form called with the bound `L` only: `A` is an
`(α, β)`-TSP-approximator for the instance `(d, p)` if, for every positive bound `L` and every `k`,
whenever some tour rooted at `p` of closed length at most `L` misses at most `k` points, `A L` is a
tour rooted at `p` of closed length at most `β L` missing at most `α k` points. -/
def IsTSPApprox (d : V → V → ℝ) (p : V) (α β : ℝ) (A : ℝ → List V) : Prop :=
  ∀ L : ℝ, 0 < L → ∀ k : ℕ, (∃ T, IsRootedTour p T ∧ tourLen d T ≤ L ∧ missed T ≤ k) →
    IsRootedTour p (A L) ∧ tourLen d (A L) ≤ β * L ∧ (missed (A L) : ℝ) ≤ α * k

/-- Proof of Corollary 4, p. 6: the penalty placed on each point when the comparison tour of length
`L` misses `k` points: `P = 2L/k` (the page's `2L/(εn)` with `εn = k`) for `k ≥ 1`, and `P = 4L`
for `k = 0`. -/
noncomputable def penalty (L : ℝ) (k : ℕ) : ℝ := if k = 0 then 4 * L else 2 * L / k

/-- Proof of Corollary 4, p. 6: the `(3, 6)`-TSP-approximator built from the prize-collecting
oracle `O`, for the bound `L`. Call `O` with the constant penalty `penalty L k` for every
`k = 0, …, |V| - 1`; among the returned tours of closed length at most `6L`, return one visiting the
most points (the first such in the order of `k`); if there is none, return `[p]`. -/
noncomputable def cor4Approx (d : V → V → ℝ) (p : V) (O : (V → ℝ) → List V) (L : ℝ) : List V := by
  classical
  exact
    match (((List.range (Fintype.card V)).map (fun k => O (fun _ => penalty L k))).filter
        (fun T => decide (tourLen d T ≤ 6 * L))).argmax (fun T => T.toFinset.card) with
    | some T => T
    | none => [p]

/-- Proof of Lemma 5, p. 6: the distance `δ` from the starting point `p` to its nearest neighbour;
`1` if `p` is the only point. -/
noncomputable def nnDist (d : V → V → ℝ) (p : V) : ℝ :=
  if h : (Finset.univ.filter (fun v => v ≠ p)).Nonempty then
    (Finset.univ.filter (fun v => v ≠ p)).inf' h (fun v => d p v)
  else 1

/-- Proof of Lemma 5, p. 6: the bound of round trip `j = 0, 1, 2, …`, namely `2^{j+1} δ` (the page's
`L = 2, 4, 8, …` with `δ` normalised to `1`). -/
noncomputable def budget (d : V → V → ℝ) (p : V) (j : ℕ) : ℝ := (2 : ℝ) ^ (j + 1) * nnDist d p

/-- Proof of Lemma 5, p. 6: the concatenation `T_0 ++ T_1 ++ ⋯ ++ T_J` of the round trips
`T_j = A (2^{j+1} δ)`. -/
noncomputable def doublingWalk (d : V → V → ℝ) (p : V) (A : ℝ → List V) (J : ℕ) : List V :=
  (List.range (J + 1)).flatMap (fun j => A (budget d p j))

/-- The run stops after round trip `J`: round trip `J` visits every point and no earlier round trip
does. -/
def StopsAt (d : V → V → ℝ) (p : V) (A : ℝ → List V) (J : ℕ) : Prop :=
  (∀ v, v ∈ A (budget d p J)) ∧ ∀ j < J, ¬ ∀ v, v ∈ A (budget d p j)

/-- The bit size of a rational `a/b` in lowest terms: `1 + ⌈log₂(|a|+1)⌉ + ⌈log₂(b+1)⌉`
(`Nat.size k = ⌈log₂(k+1)⌉`). -/
def ratSize (r : ℚ) : ℕ := 1 + Nat.size r.num.natAbs + Nat.size r.den

/-- The bit size of a rational distance matrix: the sum of the sizes of its entries. -/
def instSize (d : V → V → ℚ) : ℕ := ∑ u, ∑ v, ratSize (d u v)

end MinLatency.Approx


