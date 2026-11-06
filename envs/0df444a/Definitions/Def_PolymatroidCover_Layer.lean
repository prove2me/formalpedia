-- Prove2me | Definitions.Def_PolymatroidCover_Layer
-- name    : PolymatroidCover_Layer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:28.110565+00:00
-- url     : https://prove2.me/theorems/42d94055-f568-4239-816a-02129121f3ea
-- title:
--   Search sequence: layers $T^i = (a, j, R)$, $A_j$, $B_j$, $B(T)$
-- statement:
--   Algorithm 1 maintains a **search sequence** $T = (T^1, T^2, \dots)$. Each **layer** $T^i = (a, j, R)$ records an attempt to (re)color the **adding element** $A(T^i) = a$ with the **proposed color** $c(T^i) = j$, together with the **blocking set** $B(T^i) = R$ that blocks this attempt. For a color $j$,
--
--   $$
--   A_j := \{A(T^i) : c(T^i) = j\}, \qquad B_j := \bigcup_{i : c(T^i) = j} B(T^i), \qquad B(T) := \bigcup_i B(T^i).
--   $$
--
--   Restricted to the layers before $i$ (resp. up to $i$) these are written $A_j^{<i}, B_j^{<i}$ (resp. $A_j^{\le i}, B_j^{\le i}$).
--
--   **Formalization Note** A search sequence is a `List` of layers (structure with fields `add`, `color`, `block`), indexed from $0$: the paper's $T^i$ is `T[i-1]`, $T^{<i}$ is `T.take (i-1)` and $T^{\le i}$ is `T.take i`; `addSet`, `blockSet` and `blockUnion` compute $A_j$, $B_j$ and $B(T)$ of a list, so $A_j^{<i}$ is `addSet (T.take (i-1)) j`.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.1, pp.11–12 (PDF pp.13–14)

import Mathlib

namespace PolymatroidCover

/-- A layer `T^i = (a, j, R)` of a search sequence (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.1, printed pp.11–12 =
PDF pp.13–14): the adding element `A(T^i) = a`, the proposed color `c(T^i) = j` and the
blocking set `B(T^i) = R`. A search sequence `T = (T^1, T^2, …)` is a `List (Layer n k)`.

**Formalization Note** Lists are 0-based: the paper's layer `T^i` (`i ≥ 1`) is `T[i-1]`, the
prefix `T^{<i} = (T^1, …, T^{i−1})` is `T.take (i-1)` and `T^{≤i}` is `T.take i`. Colors are
`Fin k` (0-based). -/
structure Layer (n k : ℕ) where
  /-- the adding element `A(T^i)` -/
  add : Fin n
  /-- the proposed color `c(T^i)` -/
  color : Fin k
  /-- the blocking set `B(T^i)` -/
  block : Finset (Fin n)
  deriving DecidableEq

/-- `A_j` of a (prefix of a) search sequence (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.12 = PDF p.14): the set of
adding elements of the layers with proposed color `j`. Applied to the prefix `T.take t` it is
`A_j^{<t+1}`, and to `T.take (t+1)` it is `A_j^{≤t+1}`. -/
def addSet {n k : ℕ} (L : List (Layer n k)) (j : Fin k) : Finset (Fin n) :=
  ((L.filter (fun x => x.color = j)).map Layer.add).toFinset

/-- `B_j` of a (prefix of a) search sequence (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.12 = PDF p.14): the union of the
blocking sets of the layers with proposed color `j`. -/
def blockSet {n k : ℕ} (L : List (Layer n k)) (j : Fin k) : Finset (Fin n) :=
  ((L.filter (fun x => x.color = j)).map Layer.block).foldr (· ∪ ·) ∅

/-- `B(T) := ⋃_i B(T^i)` (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.12 = PDF p.14): the union of all blocking sets. -/
def blockUnion {n k : ℕ} (L : List (Layer n k)) : Finset (Fin n) :=
  (L.map Layer.block).foldr (· ∪ ·) ∅

end PolymatroidCover


