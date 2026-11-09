-- Prove2me | Definitions.Def_DelaunayStretch_ChainInequality
-- name    : DelaunayStretch_ChainInequality
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:33.940477+00:00
-- url     : https://prove2.me/theorems/9e3a5566-9e90-447f-bf50-8be88047d6ce
-- title:
--   Ladder graph, shortest path $P(u,v)$, prefix graphs, $\mu_i$, $\delta_i$ and the chain inequality
-- statement:
--   Let $(O_1,\dots,O_n;u,v)$ be a disk chain. For $1\le i\le n$, the **upper rail** of $O_i$ is the part of the upper arc of $O_i$ from $a_{i-1}$ to $a_i$, with length $\alpha_i$, and the **lower rail** is the part of the lower arc from $b_{i-1}$ to $b_i$, with length $\beta_i$. The **ladder graph** has the vertices $u$, $v$ and $a_i$, $b_i$ for $1\le i\le n-1$ (different labels are different vertices even when the points coincide); its edges are the $2n$ rails, weighted by their arc lengths, and the $n-1$ gates, weighted by $|G_i|$. $P(u,v)$ is the length of a shortest path from $u$ to $v$ in the ladder graph.
--
--   The vertices are arranged in columns: column $0$ is $\{u\}$, column $i$ is $\{a_i,b_i\}$, column $n$ is $\{v\}$. The $i$-th **prefix graph** is the subgraph induced by columns $0,\dots,i$. With $d^+_i$, $d^-_i$ the shortest-path lengths from $u$ to $a_i$ and to $b_i$ in the $i$-th prefix graph,
--
--   $$
--   \mu_i=\tfrac12\,(d^+_i+d^-_i),\qquad \delta_i=d^+_i-d^-_i ,
--   $$
--
--   and the cost and progress of $O_i$ are $\mu_i-\mu_{i-1}$ and $x(c_i)-x(c_{i-1})$.
--
--   For $U\in\mathbb R$, the **chain inequality holds at level $U$** if
--
--   $$
--   P(u,v)\le U\,\|u-v\|\qquad\text{for every disk chain }(O_1,\dots,O_n;u,v).
--   $$
--
--   The chain inequality is the statement to which the paper reduces the stretch bound (Theorem 2.4) and which the potential method proves (Theorems 3.9, 4.7).
--
--   **Formalization Note** Vertices are labels ($u$, $v$, $a_i$, $b_i$), so coincident points are distinct vertices; parallel edges are allowed (for $n=1$ the two rails both join $u$ and $v$). Walks are lists of edges, a walk in the $i$-th prefix graph uses only edges between vertices of columns $\le i$, and shortest-path lengths are infima of walk weights. For a disk chain all weights are nonnegative and the graph is finite, so the infimum is attained; the relevant sets of walks are nonempty. The definition is the paper's, not the recursion of Lemma 3.3.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definitions 2.2, p.12, and 3.1, p.15

import Mathlib
import Definitions.Def_DelaunayStretch_DiskChain

namespace DelaunayStretch

/-- The vertex labels of the ladder graph of a disk chain (Definition 2.2, p.12, footnote 1):
`start` is `u` (`= a₀ = b₀`), `finish` is `v` (`= aₙ = bₙ`), `up i` is `aᵢ` and `down i` is
`bᵢ` for `1 ≤ i ≤ n − 1`. Different labels are different vertices even if the points coincide. -/
inductive LadderVertex
  | start
  | finish
  | up (i : ℕ)
  | down (i : ℕ)
  deriving DecidableEq

namespace DiskChain

/-- The label of `aᵢ` (`a₀ = u`, `aₙ = v`). -/
def topV (C : DiskChain) (i : ℕ) : LadderVertex :=
  if i = 0 then .start else if i = C.n then .finish else .up i

/-- The label of `bᵢ` (`b₀ = u`, `bₙ = v`). -/
def botV (C : DiskChain) (i : ℕ) : LadderVertex :=
  if i = 0 then .start else if i = C.n then .finish else .down i

/-- The column of a vertex (§3.1, p.15): column `0` is `{u}`, column `i` is `{aᵢ, bᵢ}` for
`1 ≤ i ≤ n − 1`, column `n` is `{v}`. -/
def column (C : DiskChain) : LadderVertex → ℕ
  | .start => 0
  | .finish => C.n
  | .up i => i
  | .down i => i

/-- The length `αᵢ` of the **upper rail** of `Oᵢ`, the part of the upper arc of `Oᵢ` from
`aᵢ₋₁` to `aᵢ` (Definition 2.2, p.12). -/
noncomputable def upperRail (C : DiskChain) (i : ℕ) : ℝ :=
  (C.O i).upperArcLength (C.A (i - 1)) (C.A i)

/-- The length `βᵢ` of the **lower rail** of `Oᵢ`, the part of the lower arc of `Oᵢ` from
`bᵢ₋₁` to `bᵢ` (Definition 2.2, p.12). -/
noncomputable def lowerRail (C : DiskChain) (i : ℕ) : ℝ :=
  (C.O i).lowerArcLength (C.B (i - 1)) (C.B i)

/-- `LadderEdge C x y w`: the ladder graph of `C` has an edge between `x` and `y` of weight
`w` (Definition 2.2, p.12). The edges are the `2n` rails (the upper rail of `Oᵢ` joins
`aᵢ₋₁, aᵢ`, the lower rail joins `bᵢ₋₁, bᵢ`, `1 ≤ i ≤ n`), weighted by their arc lengths, and
the `n − 1` gates (joining `aᵢ, bᵢ`, `1 ≤ i ≤ n − 1`), weighted by `|Gᵢ|`. Edges are
undirected; parallel edges (the two rails of `O₁` when `n = 1`) are allowed. -/
def LadderEdge (C : DiskChain) (x y : LadderVertex) (w : ℝ) : Prop :=
  (∃ i, 1 ≤ i ∧ i ≤ C.n ∧
      ((x = C.topV (i - 1) ∧ y = C.topV i) ∨ (x = C.topV i ∧ y = C.topV (i - 1))) ∧
      w = C.upperRail i) ∨
  (∃ i, 1 ≤ i ∧ i ≤ C.n ∧
      ((x = C.botV (i - 1) ∧ y = C.botV i) ∨ (x = C.botV i ∧ y = C.botV (i - 1))) ∧
      w = C.lowerRail i) ∨
  (∃ i, 1 ≤ i ∧ i + 1 ≤ C.n ∧
      ((x = .up i ∧ y = .down i) ∨ (x = .down i ∧ y = .up i)) ∧ w = C.gateLength i)

/-- `LadderWalk C k x y L`: there is a walk of total weight `L` from `x` to `y` in the `k`-th
**prefix graph** of `C`, the subgraph of the ladder graph induced by the vertices of columns
`0, …, k` (Definition 3.1, p.15). For `k = n` this is the whole ladder graph. -/
inductive LadderWalk (C : DiskChain) (k : ℕ) : LadderVertex → LadderVertex → ℝ → Prop
  | nil (x : LadderVertex) : LadderWalk C k x x 0
  | cons {x y z : LadderVertex} {w L : ℝ} :
      C.LadderEdge x y w → C.column x ≤ k → C.column y ≤ k →
      LadderWalk C k y z L → LadderWalk C k x z (w + L)

/-- The length of a shortest path from `x` to `y` in the `k`-th prefix graph: the infimum of
the weights of walks.

**Formalization Note** For a disk chain all weights are nonnegative and the graph is finite,
so the infimum is attained and is the shortest-path length. The set is nonempty for the pairs
used (`u` to `aᵢ` along the upper rails, `u` to `bᵢ` along the lower rails). This is the
definition of the paper, not the recursion of Lemma 3.3. -/
noncomputable def ladderDist (C : DiskChain) (k : ℕ) (x y : LadderVertex) : ℝ :=
  sInf {L | C.LadderWalk k x y L}

/-- `P(u, v)`: the length of a shortest path from `u` to `v` in the ladder graph
(Definition 2.2, p.12). -/
noncomputable def shortestPath (C : DiskChain) : ℝ :=
  C.ladderDist C.n .start .finish

/-- `d⁺ᵢ`: the length of a shortest path from `u` to `aᵢ` in the `i`-th prefix graph
(Definition 3.1, p.15). -/
noncomputable def dPlus (C : DiskChain) (i : ℕ) : ℝ := C.ladderDist i .start (C.topV i)

/-- `d⁻ᵢ`: the length of a shortest path from `u` to `bᵢ` in the `i`-th prefix graph
(Definition 3.1, p.15). -/
noncomputable def dMinus (C : DiskChain) (i : ℕ) : ℝ := C.ladderDist i .start (C.botV i)

/-- `μᵢ = ½(d⁺ᵢ + d⁻ᵢ)` (Definition 3.1, equation (3.1), p.15). The cost of the disk `Oᵢ` is
`μᵢ − μᵢ₋₁`; its progress is `x(cᵢ) − x(cᵢ₋₁)`. -/
noncomputable def mu (C : DiskChain) (i : ℕ) : ℝ := (C.dPlus i + C.dMinus i) / 2

/-- `δᵢ = d⁺ᵢ − d⁻ᵢ` (Definition 3.1, equation (3.1), p.15). -/
noncomputable def delta (C : DiskChain) (i : ℕ) : ℝ := C.dPlus i - C.dMinus i

end DiskChain

/-- The **chain inequality holds at level `U`** (Definition 2.2, p.12): `P(u, v) ≤ U ‖u − v‖`
for every disk chain `(O₁, …, Oₙ; u, v)`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definitions 2.2, p.12, and 3.1, p.15.

**Formalization Note** The ladder graph has the labels of `LadderVertex` as vertices (so
coincident points stay distinct, footnote 1), rail weights are arc lengths through the angle
parameters of `Disk`, and `P(u, v)` is the infimum of walk weights (`DiskChain.shortestPath`).
-/
def ChainInequality (U : ℝ) : Prop :=
  ∀ C : DiskChain, C.IsDiskChain → C.shortestPath ≤ U * dist C.u C.v

end DelaunayStretch


