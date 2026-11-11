-- Prove2me | Definitions.Def_DynMaxMatchEC_Main_Blocks
-- name    : DynMaxMatchEC_Main_Blocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:02:19.72285+00:00
-- url     : https://prove2.me/theorems/2d70742c-5753-4bde-b6dd-10deda3cdb78
-- title:
--   Block-respecting outputs: the low-degree set of Theorem 2.5 and the (z, x)-subgraph system of Definitions 3.1–3.2
-- statement:
--   The timeline of a dynamic algorithm is cut into **blocks** of exactly $b$ updates, the last possibly shorter: block $j\ge1$ consists of updates $(j-1)b+1,\dots,jb$. It begins once update $(j-1)b$ has been processed (preprocessing for $j=1$) and ends once update $jb$ has been processed.
--
--   A set maintained at block ends is read from the program's output records (triples `tag, a, b`): an initial set (preprocessing output), and, written at the beginning of block $j$ (that is, while processing update $(j-1)b$, or in preprocessing for $j=1$), the vertices that leave and that join the set at the end of block $j$. After $t$ updates the set is the initial one with the moves of the $\lfloor t/b\rfloor$ finished blocks applied in order (`blockSet`); so it changes only at block ends and only by announced vertices. `segment confs j` is the output written in step $j$ of a history (preprocessing for $j=0$, update $j$ otherwise), and `announced n b k confs j` the vertices with tag $k$ announced for block $j$.
--
--   **Theorem 2.5** (block length $\delta$): tag $0$ is "in the initial $A$", tag $1$ is $A^-_B$ (leaves $A$), tag $2$ is $A^+_B$ (joins $A$); `lowSet` is the set $A$ after $t$ updates.
--
--   **Theorem 3.3** (block length $x$): tag $0$ inserts the edge $ab$ into $M$, tag $1$ deletes it (`sysM`, from $\emptyset$); tag $2$ is "in the initial $S$", tag $3$ is $U_B$ (moves $U\to S$), tag $4$ is $S_B$ (moves $S\to U$); `sysS` is $S$ after $t$ updates and $U=V\setminus S$.
--
--   **Definition 3.1.** For a graph $G$ on $n$ vertices and parameters $x,z$, a partition $(S,U)$ and $M\subseteq E(G)$ form a **$(z,x)$-subgraph system with constant $c$** if, with $m(v)$ the number of edges of $M$ at $v$: (P1) $m(v)\le z$ for every $v$; (P2) $m(v)\ge z-c\,x\log_2 n$ for $v\in S$; (P3) $|N_G(u)\cap U|\le16z$ for $u\in U$. The conditions $1\le x\le z\le n$, powers of $2$, are hypotheses of the theorems that use it, and $c\ge1$ is quantified there.
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 13, §2.5 and Theorem 2.5; p. 14, Definition 3.1; p. 16, Definition 3.2 and Theorem 3.3

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynMaxMatchEC_Main_Model

namespace DynMaxMatchEC.Main

open DynBrooks

/-!
# Block-respecting outputs: the low-degree set (Theorem 2.5) and the subgraph system (Definitions
3.1, 3.2)

Chuzhoy, *New Algorithms for Dynamic Maximal Matching and Edge Coloring* (manuscript, Nov. 1,
2026; PDF sha256 2c277528…4ca5), §2.5 pp. 13–14 (Theorem 2.5), §3.1 p. 14 (Definition 3.1), p. 16
(Definition 3.2, Theorem 3.3).

* The timeline is cut into blocks of exactly `b` updates (the last may be shorter): block `j ≥ 1`
  consists of updates `(j-1)·b + 1, …, j·b`. Block `j` begins when update `(j-1)·b` has been
  processed (preprocessing for `j = 1`) and ends when update `j·b` has been processed.
* `segment confs j` is the list of words written during step `j` of a history: by preprocessing for
  `j = 0`, while processing update `j` for `j ≥ 1` (outputs are append-only).
* Outputs are read as triples `tag, a, b` (`triples`). A vertex record `tag, v, _` names the vertex
  `v` if `v < n`.
* **A set maintained at block ends.** The algorithm reports an initial set (records with the initial
  tag, in the preprocessing output) and, at the beginning of block `j` (in the output of step
  `(j-1)·b`), the vertices that will leave and that will join the set at the end of block `j`. After
  `t` updates the set is the initial one with the moves of the `⌊t/b⌋` completed blocks applied in
  order. So the set changes only at block ends, and only by the announced vertices.
* **Theorem 2.5's output** (block length `δ`): tag `0` = in the initial `A`; tag `1` = in `A⁻_B`
  (leaves `A`); tag `2` = in `A⁺_B` (joins `A`).
* **Theorem 3.3's output** (block length `x`): tag `0` = edge `ab` inserted into `M`; tag `1` = edge
  `ab` deleted from `M`; tag `2` = `a` in the initial `S`; tag `3` = `a ∈ U_B` (moves from `U` to
  `S`); tag `4` = `a ∈ S_B` (moves from `S` to `U`). `U` is the complement of `S`.
-/

/-- The words written during step `j` of the history `confs = [c₀, c₁, …]`: the preprocessing
output for `j = 0`, and the words written while processing update `j` for `j ≥ 1`. -/
def segment {w : ℕ} (confs : List (Config w)) : ℕ → List ℕ
  | 0 =>
      match confs[0]? with
      | some c => c.output
      | none => []
  | j + 1 =>
      match confs[j + 1]?, confs[j]? with
      | some c', some c => c'.output.drop c.output.length
      | _, _ => []

/-- The vertices `v < n` named by the records `k, v, _` of `out`. -/
def taggedVertices (n k : ℕ) (out : List ℕ) : Finset (Fin n) :=
  ((triples out).filterMap fun r => if h : r.1 = k ∧ r.2.1 < n then some ⟨r.2.1, h.2⟩ else none).toFinset

/-- The number of records of `out` with tag `k`. -/
def countTag (k : ℕ) (out : List ℕ) : ℕ :=
  ((triples out).filter fun r => r.1 = k).length

/-- A set changed only at block ends: `init` with, for blocks `1, …, j` in order, the vertices
`leave i` removed and the vertices `join i` added. -/
def blockSet {n : ℕ} (init : Finset (Fin n)) (leave join : ℕ → Finset (Fin n)) :
    ℕ → Finset (Fin n)
  | 0 => init
  | j + 1 => (blockSet init leave join j \ leave (j + 1)) ∪ join (j + 1)

/-- The vertices announced with tag `k` at the beginning of block `j` (block length `b`). -/
def announced {w : ℕ} (n b k : ℕ) (confs : List (Config w)) (j : ℕ) : Finset (Fin n) :=
  taggedVertices n k (segment confs ((j - 1) * b))

/-- Theorem 2.5: the set `A` after `t` updates (block length `δ`). -/
def lowSet {w : ℕ} (n δ : ℕ) (confs : List (Config w)) (t : ℕ) : Finset (Fin n) :=
  blockSet (taggedVertices n 0 (segment confs 0)) (announced n δ 1 confs) (announced n δ 2 confs)
    (t / δ)

/-- Theorem 3.3: the set `S` after `t` updates (block length `x`); `U` is its complement. -/
def sysS {w : ℕ} (n x : ℕ) (confs : List (Config w)) (t : ℕ) : Finset (Fin n) :=
  blockSet (taggedVertices n 2 (segment confs 0)) (announced n x 4 confs) (announced n x 3 confs)
    (t / x)

/-- Apply one record of Theorem 3.3's output to the edge set `M`: tag `0` inserts the edge `ab`,
tag `1` deletes it, other tags leave `M` unchanged. -/
def applySysRecord {n : ℕ} (M : Finset (Sym2 (Fin n))) : ℕ × ℕ × ℕ → Finset (Sym2 (Fin n))
  | (k, a, b) =>
      match toEdge n a b with
      | some e => if k = 0 then insert e M else if k = 1 then M.erase e else M
      | none => M

/-- Theorem 3.3: the edge set `M` reported by the output so far (from `∅`). -/
def sysM (n : ℕ) (out : List ℕ) : Finset (Sym2 (Fin n)) :=
  (triples out).foldl applySysRecord ∅

open Classical in
/-- Definition 3.1: `(S, U = V \ S, M)` is a `(z, x)`-subgraph system for `G` with the constant
`c`: `M ⊆ E(G)`; (P1) `m(v) ≤ z` for every `v`; (P2) `m(v) ≥ z − c·x·log₂ n` for `v ∈ S`; (P3)
`|N_G(u) ∩ U| ≤ 16z` for `u ∈ U`. (The conditions on `x, z` are hypotheses of the theorems.) -/
noncomputable def IsSubgraphSystem {n : ℕ} (c : ℝ) (z x : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (M : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    (∀ v : Fin n, mdeg M v ≤ z) ∧
    (∀ v ∈ S, (z : ℝ) - c * x * Real.logb 2 n ≤ mdeg M v) ∧
    (∀ u : Fin n, u ∉ S →
      (Finset.univ.filter fun u' => G.Adj u u' ∧ u' ∉ S).card ≤ 16 * z)

end DynMaxMatchEC.Main


