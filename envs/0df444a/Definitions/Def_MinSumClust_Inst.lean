-- Prove2me | Definitions.Def_MinSumClust_Inst
-- name    : MinSumClust_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:20.800377+00:00
-- url     : https://prove2.me/theorems/061f2af9-e323-4d70-b1dc-03acde003ca0
-- title:
--   A min-sum $k$-clustering instance and well-formedness
-- statement:
--   An **instance** of min-sum $k$-clustering consists of an integer $k$ and a table of rational distances $(d(i,j))_{i,j}$; its clients are $D=\{0,\dots,n-1\}$ where $n$ is the number of rows. The instance is **well formed** if
--
--   1. every row has length $n$;
--   2. $d$ is a metric on the $n$ clients (zero diagonal, symmetric, positive off the diagonal, triangle inequality);
--   3. $1\le k\le n$.
--
--   This is exactly the input described on p.1: "a collection $D$ of $n$ elements, the clients, with (finite) metric distances … and a positive integer $k\le n$". No legitimate input is excluded ($n=1$, $k=1$ and $k=n$ are instances).
--
--   **Formalization Note** An instance is raw data so that it can be the input of a Turing machine; well-formedness is a separate predicate, and the guarantees of Theorems 1 and 2 are stated for well-formed instances only. Distances are rationals written in binary.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), §1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric

namespace MinSumClust

/-- **A min-sum k-clustering instance**, §1, p.1.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), §1, p.1: "a collection D of n elements, the clients, with
(finite) metric distances d(u, v) ≥ 0 … and a positive integer k ≤ n".

**Formalization Note.** An instance is raw input data: the number `k` and a rational distance
table `dist` (row `i`, column `j`). Clients are `Fin n` with `n = dist.length`. Whether the data is
a legitimate instance is the separate predicate `Inst.WellFormed`; statements quantify over
well-formed instances only, and malformed data may receive any output. -/
structure Inst where
  /-- the number of clusters -/
  k : ℕ
  /-- the distance table, row by row -/
  dist : List (List ℚ)

namespace Inst

/-- The number of clients `n`. -/
def n (I : Inst) : ℕ := I.dist.length

/-- The rational distance `d(i, j)`, read from the table (`0` outside the table). -/
def d (I : Inst) (i j : Fin I.n) : ℚ := (I.dist.getD i.val []).getD j.val 0

/-- The distance as a real number, for the cost and the guarantees. -/
noncomputable def dR (I : Inst) (i j : Fin I.n) : ℝ := (I.d i j : ℝ)

/-- **Well-formed instance**, §1, p.1: every row has length `n`, the distances form a metric on
the `n` clients, and `1 ≤ k ≤ n`.

**Formalization Note.** Nothing else is excluded: `n = 1`, `k = 1` and `k = n` are instances. -/
def WellFormed (I : Inst) : Prop :=
  (∀ r ∈ I.dist, r.length = I.n) ∧ IsMetric I.dR ∧ 1 ≤ I.k ∧ I.k ≤ I.n

end Inst

end MinSumClust


