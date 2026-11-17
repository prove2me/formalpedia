-- Prove2me | Definitions.Def_BipDijoin_Supplement_capWords
-- name    : BipDijoin_Supplement_capWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:50:38.714844+00:00
-- url     : https://prove2.me/theorems/01c88a96-8612-4e98-8e45-3471260af5eb
-- title:
--   Local-access input layout of the routing theorem: unit $\varepsilon$, sparse supply, vertex and arc records
-- statement:
--   The input of the local routing theorem (Theorem 5.2) on the word RAM, following the conventions of §5.1: "Supply is listed sparsely. At an encountered vertex we can query $\nabla(v)$ and read its original outgoing list in $O(1+\deg^+_G(v))$ time … Rational capacities are given as integer multiples of a supplied common rational unit $\varepsilon>0$."
--
--   **Data.** A unit $\varepsilon=e_n/e_d>0$; for each vertex $v=0,\dots,n-1$ a pair $(s_v,\mathrm{out}_v)$ with $\nabla(v)=s_v\varepsilon$, where $\mathrm{out}_v$ lists the arcs leaving $v$ as pairs $(\text{head},k)$ of capacity $k\varepsilon$; a sparse list of pairs $(v,t_v)$, $t_v>0$, distinct $v$, with $\Delta(v)=t_v\varepsilon$ (unlisted vertices have $\Delta(v)=0$); and an integer $\nu\ge1$. Arc $j$ is the $j$-th arc of $\mathrm{out}_0\,\mathrm{out}_1\cdots$, so the arcs of $v$ have consecutive indices starting at $p_v=\sum_{u<v}\deg^+(u)$. All multipliers are natural numbers.
--
--   **Input words.** $n,\ m,\ \nu,\ e_n,\ e_d,$ the number of supply pairs, the pairs $v,t_v$, then for each vertex the record $s_v,\ \deg^+(v),\ p_v$ (three words at a fixed offset), then for each arc the two words $\text{head},k$. Each vertex record and each arc record is reachable in $O(1)$ steps from the header, and no part of the input requires a scan of the graph to be located.
--
--   **Output words.** The number of listed flow entries, then triples $j,p,q$ meaning that arc $j$ carries $p/q$ ($q>0$, distinct $j$; unlisted arcs carry $0$), then $|S|$ and the vertices of $S$.
--
--   **Outcome.** The guarantee of Theorem 5.2 for an output $(f,S)$: there are witnesses $a,b$ that $f$ partially routes $\Delta$ and respects $\nabla$, such that $f(uv)>0$ implies $b(u)=\nabla(u)$, and exactly one of $\Delta(S)>c(\delta^+(S))+\nabla(S)$ and ($a=\Delta$ and $S=\emptyset$) holds.
--
--   **Formalization Note** Every nonnegative rational instance has such a representation (take $\varepsilon=1/D$ for a common denominator $D$). The largest input word bounds every number in the input and appears in the width condition and the logarithmic factor of Theorem 5.2.
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), §5.1, p.15 (PDF p.17), input and routing conventions; Theorem 5.2, pp.15–16 (PDF pp.17–18)

import Mathlib
import Definitions.Def_BipDijoin_Supplement_CapNet

set_option autoImplicit false

namespace BipDijoin

namespace Supplement

/-!
# The local-access input layout of Theorem 5.2, and its output

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), §5.1, p.15 (PDF p.17):
"Supply is listed sparsely. At an encountered vertex we can query ∇(v) and read its original
outgoing list in O(1 + deg⁺_G(v)) time; arc records give their heads and capacities. No original
incoming list is required. Rational capacities are given as integer multiples of a supplied common
rational unit ε > 0; this unit is known without scanning the graph. Numerical bit lengths and
logarithmic factors are included in Õ." Definition 5.1: "All flows and sets are represented
sparsely, with omitted flow entries equal to zero."

**Formalization Note.**
* **Input data.** `verts` lists, for each vertex `v = 0, …, n − 1`, the pair `(s_v, out_v)`: the
  sink capacity is `∇(v) = s_v · ε`, and `out_v` lists the arcs leaving `v` as pairs `(head, k)`
  with capacity `k · ε`. The unit is `ε = en / ed`. `sup` lists the supply sparsely as pairs
  `(v, t_v)` with `∆(v) = t_v · ε > 0`; vertices not listed have `∆(v) = 0`. `ν` is the integer of
  Theorem 5.2. Every multiplier is a natural number, so every capacity is a nonnegative rational,
  and every nonnegative rational instance has such a representation (take `ε = 1/D` for a common
  denominator `D`).
* **Arc indices.** Arc `j` is the `j`-th arc of the concatenation `out_0 ++ out_1 ++ ⋯`, so the
  arcs of `v` have the consecutive indices `p_v, …, p_v + deg⁺(v) − 1`, `p_v = Σ_{u<v} deg⁺(u)`.
* **Input words** (`capWords`): `n, m, ν, en, ed, |sup|`, the pairs `v, t_v` of `sup`, then for each
  vertex `v` its record `s_v, deg⁺(v), p_v` (three words, at a fixed offset from `v`), then for each
  arc `j` the two words `head_j, k_j`. Every vertex record and every arc record is reachable in
  `O(1)` steps from the header, and the out-list of `v` is read in `O(1 + deg⁺(v))` steps; no part
  of the input needs a scan of the graph to be located.
* **Output words** (`DecodesFlowCut`): the number of listed flow entries, then for each the three
  words `j, p, q` (arc `j` carries `p / q`, `q > 0`); unlisted arcs carry `0`. Then `|S|` and the
  vertices of `S`.
-/

/-- The unit `ε = en / ed`. -/
def epsOf (en ed : ℕ) : ℚ := (en : ℚ) / ed

/-- The arcs of the input, in index order, as `(tail, head, k)`. -/
def capArcs (verts : List (ℕ × List (ℕ × ℕ))) : List (ℕ × ℕ × ℕ) :=
  (List.range verts.length).flatMap
    (fun v => ((verts.getD v (0, [])).2).map (fun p => (v, p.1, p.2)))

/-- The capacitated multidigraph of the input data: vertices `0, …, n − 1`, arc capacities
`k · ε`, supply `∆(v) = t_v · ε` from the sparse list, sink capacity `∇(v) = s_v · ε`. -/
def capNetOf (verts : List (ℕ × List (ℕ × ℕ))) (en ed : ℕ) (sup : List (ℕ × ℕ)) : CapNet where
  n := verts.length
  arcs := (capArcs verts).map (fun t => (t.1, t.2.1, (t.2.2 : ℚ) * epsOf en ed))
  supply := fun v => ((sup.filter (fun p => p.1 = v)).map (fun p => (p.2 : ℚ) * epsOf en ed)).sum
  sinkCap := fun v => ((verts.getD v (0, [])).1 : ℚ) * epsOf en ed

/-- Well-formed input data: `ε > 0`, `ν ≥ 1`, every head is a vertex, and the supply list names
distinct vertices with positive multipliers. -/
def ValidCap (verts : List (ℕ × List (ℕ × ℕ))) (en ed : ℕ) (sup : List (ℕ × ℕ)) (ν : ℕ) : Prop :=
  0 < en ∧ 0 < ed ∧ 1 ≤ ν ∧ (∀ r ∈ verts, ∀ p ∈ r.2, p.1 < verts.length) ∧
    (∀ p ∈ sup, p.1 < verts.length ∧ 0 < p.2) ∧ (sup.map Prod.fst).Nodup

/-- `p_v`: the index of the first arc leaving `v`. -/
def firstArc (verts : List (ℕ × List (ℕ × ℕ))) (v : ℕ) : ℕ :=
  ((verts.take v).map (fun r => r.2.length)).sum

/-- The input words of Theorem 5.2 (see the Formalization Note). -/
def capWords (verts : List (ℕ × List (ℕ × ℕ))) (en ed : ℕ) (sup : List (ℕ × ℕ)) (ν : ℕ) :
    List ℕ :=
  [verts.length, (capArcs verts).length, ν, en, ed, sup.length] ++
    sup.flatMap (fun p => [p.1, p.2]) ++
    (List.range verts.length).flatMap (fun v =>
      [(verts.getD v (0, [])).1, (verts.getD v (0, [])).2.length, firstArc verts v]) ++
    (verts.flatMap (fun r => r.2)).flatMap (fun p => [p.1, p.2])

/-- The largest word of a list (`0` for the empty list). -/
def maxWord (l : List ℕ) : ℕ := l.foldr max 0

/-- The words `ws` encode the flow `f` (sparsely, as rationals `p / q`) and the vertex set `S` of
the network `N`. -/
def DecodesFlowCut (N : CapNet) (ws : List ℕ) (f : ℕ → ℚ) (S : Finset ℕ) : Prop :=
  ∃ (fl : List (ℕ × ℕ × ℕ)) (Sl : List ℕ),
    ws = (fl.length :: fl.flatMap (fun t => [t.1, t.2.1, t.2.2])) ++ (Sl.length :: Sl) ∧
    (fl.map Prod.fst).Nodup ∧ (∀ t ∈ fl, t.1 < N.m ∧ 0 < t.2.2) ∧
    Sl.Nodup ∧ (∀ v ∈ Sl, v < N.n) ∧ S = Sl.toFinset ∧
    ∀ j, f j = ((fl.filter (fun t => t.1 = j)).map (fun t => (t.2.1 : ℚ) / t.2.2)).sum

/-- The guarantee of Theorem 5.2 for the output `(f, S)`: for some routed supply `a` and absorbed
flow `b` witnessing that `f` partially routes `∆` and respects `∇`, a vertex forwards flow on an
arc only if its sink capacity is saturated (`f(uv) > 0 → b(u) = ∇(u)`), and exactly one of
(1) `∆(S) > c(δ⁺(S)) + ∇(S)` (excess remains) and (2) `a = ∆` (the routing is full) and `S = ∅`
holds. -/
def LocalRoutingOutcome (N : CapNet) (f : ℕ → ℚ) (S : Finset ℕ) : Prop :=
  ∃ a b, N.IsRouting f a b ∧ (∀ j < N.m, 0 < f j → b (N.tail j) = N.sinkCap (N.tail j)) ∧
    Xor (N.setSupply S > N.cutCap S + N.setSink S) ((∀ v < N.n, a v = N.supply v) ∧ S = ∅)

end Supplement

end BipDijoin


