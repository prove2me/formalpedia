-- Prove2me | Definitions.Def_BipDijoin_ofInput
-- name    : BipDijoin_ofInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:49:14.66342+00:00
-- url     : https://prove2.me/theorems/9c3e0e54-cf28-4824-a06b-2a42dd1cd56c
-- title:
--   Input and output layouts: arc lists, dijoin and dicut-packing output, decomposition output
-- statement:
--   **Input.** A bipartite multidigraph with left vertices $0,\dots,a-1$, right vertices $0,\dots,b-1$ and arcs $\ell_j\to r_j$ ($j<m$) is given as the words
--   $$a,\ b,\ m,\ \ell_0,\ r_0,\ \dots,\ \ell_{m-1},\ r_{m-1},$$
--   with every $\ell_j<a$ and $r_j<b$. As a graph, left vertex $\ell$ is named $\ell$, right vertex $r$ is named $a+r$, and arc $j$ is the edge identity $j$; so $n=a+b$ and parallel arcs are allowed.
--
--   **Dijoin output.** The words $|B|$, the arc indices of $B$, the number $k$ of dicuts, then each dicut as its size followed by its arc indices. They are correct if $B$ is a minimum dijoin and the $k$ dicuts form a maximum dicut packing.
--
--   **Decomposition output.** The number of records, then for each record $s,\ |U|,\ U,\ |P|,\ P$ with $s=0$ for a source end and $s=1$ for a sink end; $U$ lists vertices of the current graph (original names below $n$, the $i$-th contracted vertex named $n+i$) and $P$ lists edge identities. Correct if the records form a relaxed end decomposition. The partial variant appends $|N|,\ N$ for a perfect matching $N$ of the final graph $H$ and requires $|V(H)|\le|V(G)|-\alpha(G)$.
--
--   **Formalization Note** Disjoint dicuts have total size at most $m$, so listing their arcs costs no more than the paper's laminar representation. Records name contracted sets in current vertex names, as the paper's compact contraction records do.
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Theorem 1.1, p.1 (PDF p.3); Theorem 3.5, p.7 (PDF p.9); Theorem 4.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsDicut
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsPartialDecomp

set_option autoImplicit false

namespace BipDijoin

/-!
# Input and output layouts of the algorithms

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6): Theorem 1.1, p.1
(PDF p.3), "given a bipartite digraph D = (L ⊎ R, E) with n vertices and m edges, all directed from
L to R, computes a minimum dijoin and a maximum dicut packing"; Theorem 4.2, p.9 (PDF p.11),
"outputs a relaxed bipartite end decomposition of G"; Theorem 3.5, p.7 (PDF p.9), "outputs a
partial relaxed bipartite end decomposition ending with a bipartite graph H, together with a
perfect matching of H".

**Formalization Note.**
* **Input.** A bipartite multidigraph with `L = {0, …, a − 1}`, `R = {0, …, b − 1}` and arcs
  `ℓ_j → r_j` (`j < m`) is the word list `a, b, m, ℓ₀, r₀, …, ℓ_{m−1}, r_{m−1}` (`inputWords`).
  `ValidInput` says every `ℓ_j < a` and `r_j < b`. As a `BipGraph` (`ofInput`), left vertex `ℓ` is
  `ℓ`, right vertex `r` is `a + r`, and arc `j` is the edge identity `j`; so `n = a + b`, and
  parallel arcs are allowed.
* **Dijoin output** (`SolvesDijoin`): `|B|`, the arc indices of `B`, the number `k` of dicuts, then
  each dicut as its size followed by its arc indices. `B` must be a minimum dijoin and the `k`
  dicuts a maximum dicut packing. Disjoint dicuts have total size at most `m`.
* **Decomposition output** (`DecodesDecomp`): the number of records, then for each record
  `s, |U|, U, |P|, P`, where `s = 0` for a source end and `1` for a sink end, `U` lists vertices of
  the current graph (original ids `< n`, the `i`-th representative is `n + i`) and `P` lists edge
  identities. Listing `U` in current ids keeps the output size linear in the work done.
* **Partial decomposition with perfect matching** (`DecodesPartialPM`): the records, then
  `|N|, N` for a perfect matching `N` of the final graph `H`, and `|V(H)| + α(G) ≤ |V(G)|`
  (written additively, to avoid natural-number subtraction).
-/

/-- The input words `a, b, m, ℓ₀, r₀, …, ℓ_{m−1}, r_{m−1}`. -/
def inputWords (a b : ℕ) (es : List (ℕ × ℕ)) : List ℕ :=
  [a, b, es.length] ++ es.flatMap (fun p => [p.1, p.2])

/-- Every arc joins a left vertex `< a` to a right vertex `< b`. -/
def ValidInput (a b : ℕ) (es : List (ℕ × ℕ)) : Prop := ∀ p ∈ es, p.1 < a ∧ p.2 < b

/-- The bipartite multigraph of an input: vertices `0, …, a + b − 1` (left `ℓ < a`, right `a + r`),
edge identities `0, …, m − 1`, arc `j` from `ℓ_j` to `a + r_j`. -/
def ofInput (a b : ℕ) (es : List (ℕ × ℕ)) : BipGraph where
  V := Finset.range (a + b)
  E := Finset.range es.length
  isLeft := fun v => decide (v < a)
  tl := fun j => (es.getD j (0, 0)).1
  hd := fun j => a + (es.getD j (0, 0)).2

/-- The output words of a dijoin `B` and a list of dicuts `Cs`. -/
def encodeSol (B : List ℕ) (Cs : List (List ℕ)) : List ℕ :=
  (B.length :: B) ++ (Cs.length :: Cs.flatMap (fun C => C.length :: C))

/-- The words `ws` encode a minimum dijoin and a maximum dicut packing of `G`. -/
def SolvesDijoin (G : BipGraph) (ws : List ℕ) : Prop :=
  ∃ (B : List ℕ) (Cs : List (List ℕ)), ws = encodeSol B Cs ∧ B.Nodup ∧ (∀ C ∈ Cs, C.Nodup) ∧
    G.IsMinDijoin B.toFinset ∧ G.IsMaxDicutPacking (Cs.map List.toFinset)

/-- The words `ws` encode the record `r` as `s, |U|, U, |P|, P` (`s = 0` source, `1` sink). -/
def RecWords (r : Rec) (ws : List ℕ) : Prop :=
  ∃ Ul Pl : List ℕ, Ul.Nodup ∧ Pl.Nodup ∧ Ul.toFinset = r.U ∧ Pl.toFinset = r.P ∧
    ws = [if r.left then 0 else 1, Ul.length] ++ Ul ++ [Pl.length] ++ Pl

/-- The words `ws` encode a relaxed bipartite end decomposition of `G` with representatives
`n, n + 1, …`. -/
def DecodesDecomp (G : BipGraph) (n : ℕ) (ws : List ℕ) : Prop :=
  ∃ (recs : List Rec) (chunks : List (List ℕ)), List.Forall₂ RecWords recs chunks ∧
    ws = recs.length :: chunks.flatten ∧ IsDecomp false G n recs

/-- The words `ws` encode a partial relaxed bipartite end decomposition of `G` (representatives
`n, n + 1, …`) ending at a graph `H`, then a perfect matching `N` of `H`, and
`|V(H)| ≤ |V(G)| − α(G)`. -/
def DecodesPartialPM (G : BipGraph) (n : ℕ) (ws : List ℕ) : Prop :=
  ∃ (recs : List Rec) (chunks : List (List ℕ)) (Nl : List ℕ) (H : BipGraph),
    List.Forall₂ RecWords recs chunks ∧ ws = recs.length :: chunks.flatten ++ (Nl.length :: Nl) ∧
    Nl.Nodup ∧ IsPartialDecomp false G n recs H ∧ H.IsPerfectMatching Nl.toFinset ∧
    H.V.card + G.deficiency ≤ G.V.card

end BipDijoin


