-- Prove2me | Definitions.Def_BipDijoin_Supplement_localWords
-- name    : BipDijoin_Supplement_localWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:51:01.122287+00:00
-- url     : https://prove2.me/theorems/4335d8ef-a754-4cf8-8a30-2b8a515bc660
-- title:
--   Local-access input layout of Local-Strong-End: simple bipartite graph in CSR form, mate array, terminal list
-- statement:
--   The input of Local-Strong-End (Theorem 3.4) on the word RAM. Its running time $\tilde O(\sigma^3|T|^{1.5})$ does not grow with the size of the graph, so the graph is read locally, as in §5.1 ("at an encountered vertex we can … read its original outgoing list in $O(1+\deg^+_G(v))$ time"), and it is simple, as in §5.2 ("We suppress parallel edges, which do not change the strong ends").
--
--   **Graph.** Left vertices $0,\dots,a-1$, right vertices $a,\dots,a+b-1$; $\mathrm{nbrs}[v]$ lists the neighbours of $v$ (without repetition, on the other side, symmetric). The edge $\ell r$ has the identity $\ell\,(a+b)+r$, so it is determined by its ends.
--
--   **Matching.** A mate array: $\mathrm{mate}[v]=0$ if $v$ is unmatched and $u+1$ if $v$ is matched to $u$ (symmetric, along edges). The matching $M$ consists of the edges $\ell\,\mathrm{mate}[\ell]-1$ of the matched left vertices.
--
--   **Input words.** $a,\ b,\ \sigma,\ |T|$, the list $T$, the $n+1$ offsets $o_v=\sum_{u<v}|\mathrm{nbrs}[u]|$, the $n$ mate words, and the concatenated neighbour lists ($n=a+b$). Every vertex's neighbour list and mate are reachable in $O(1)$ steps.
--
--   **Output.** Either the single word $0$ (the answer $\bot$), required to come with "every strong end has at least $\sigma$ vertices"; or $1,\ |U|$, the vertices of $U$, then $|D|$ and the end pairs $\ell,r$ of the edges of $D=M'\mathbin{\triangle}M$, required to satisfy: $M'$ is a matching with $|M'|\ge|M|$, $|U|\ge2$, $U$ is a source or sink strongly connected component of the alternating digraph $G_{M'}$, and $M'$ fits $U$.
--
--   **Formalization Note** The new matching is given by its changes, as the matchings of Lemma 5.10 are "represented … as changes to the shared matching $M_0$".
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Theorem 3.4, p.5 (PDF p.7); §5.1, p.15 (PDF p.17); §5.2, p.18 (PDF p.20); Lemma 5.10, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsStrongEnd

set_option autoImplicit false

namespace BipDijoin

namespace Supplement

/-!
# The local-access input layout of Theorem 3.4, and its output

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), Theorem 3.4, p.5
(PDF p.7), restated p.15 (PDF p.17) and p.20 (PDF p.22): Local-Strong-End "takes as input a
bipartite graph G, a terminal set T ⊆ V …, a matching M whose unmatched set is T, and an integer
σ ≥ 2, and either finds an extremal SCC U and a matching M′ with |M′| ≥ |M| that fits U, or returns
U = M′ = ⊥". §5.2, p.18 (PDF p.20): "We suppress parallel edges, which do not change the strong
ends". The time bound Õ(σ³|T|^{1.5}) does not depend on n or m, so the input is accessed locally:
§5.1, p.15, "At an encountered vertex we can … read its original outgoing list in
O(1 + deg⁺_G(v)) time"; Lemma 5.10, p.20, matchings are "represented as … changes to" a matching.

**Formalization Note.**
* **Graph.** `L = {0, …, a − 1}`, `R = {a, …, a + b − 1}`; `nbrs[v]` lists the neighbours of `v`
  (right neighbours of a left vertex, left neighbours of a right vertex). The graph is simple:
  the edge `ℓr` has the identity `ℓ · (a + b) + r` (`localGraph`), so its two ends determine it.
* **Matching.** `mate[v] = 0` if `v` is unmatched and `u + 1` if `v` is matched to `u`
  (`localMatching` collects the edges `ℓ · (a + b) + (mate[ℓ] − 1)` of the matched left vertices).
* **Validity** (`ValidLocal`): the adjacency lists have the right lengths and sides, no repeats,
  and are symmetric; the mate array is symmetric and uses edges.
* **Input words** (`localWords`): `a, b, σ, |T|`, the list `T`, the `n + 1` offsets
  `o_v = Σ_{u<v} |nbrs[u]|`, the `n` mate words, then the concatenated neighbour lists
  (CSR layout, `n = a + b`). Every vertex's neighbour list and mate is reachable in `O(1)` steps
  from the header.
* **Output words** (`LocalEndOutput`): `0` for `⊥`, or `1, |U|`, the vertices of `U`, then `|D|`
  and the pairs `ℓ, r` of the edges of `D = M′ ∆ M` (the new matching given by its changes).
-/

/-- The simple bipartite graph of the adjacency lists: vertices `0, …, a + b − 1` (left `v < a`),
the edge `ℓr` (`ℓ < a`, `r ∈ nbrs[ℓ]`) with identity `ℓ · (a + b) + r`. -/
def localGraph (a b : ℕ) (nbrs : List (List ℕ)) : BipGraph where
  V := Finset.range (a + b)
  E := (Finset.range a).biUnion
    (fun ℓ => ((nbrs.getD ℓ []).toFinset).image (fun r => ℓ * (a + b) + r))
  isLeft := fun v => decide (v < a)
  tl := fun e => e / (a + b)
  hd := fun e => e % (a + b)

/-- The matching of the mate array: the edges `ℓ · (a + b) + (mate[ℓ] − 1)` of the matched left
vertices `ℓ`. -/
def localMatching (a b : ℕ) (mate : List ℕ) : Finset ℕ :=
  ((Finset.range a).filter (fun ℓ => mate.getD ℓ 0 ≠ 0)).image
    (fun ℓ => ℓ * (a + b) + (mate.getD ℓ 0 - 1))

/-- Well-formed adjacency lists and mate array. -/
def ValidLocal (a b : ℕ) (nbrs : List (List ℕ)) (mate : List ℕ) : Prop :=
  nbrs.length = a + b ∧ mate.length = a + b ∧
    (∀ v < a + b, (nbrs.getD v []).Nodup) ∧
    (∀ ℓ < a, ∀ r ∈ nbrs.getD ℓ [], a ≤ r ∧ r < a + b) ∧
    (∀ r < a + b, a ≤ r → ∀ ℓ ∈ nbrs.getD r [], ℓ < a) ∧
    (∀ u < a + b, ∀ v < a + b, u ∈ nbrs.getD v [] ↔ v ∈ nbrs.getD u []) ∧
    (∀ v < a + b, ∀ u, mate.getD v 0 = u + 1 →
      u < a + b ∧ u ∈ nbrs.getD v [] ∧ mate.getD u 0 = v + 1)

/-- The input words of Theorem 3.4 (see the Formalization Note). -/
def localWords (a b σ : ℕ) (T : List ℕ) (nbrs : List (List ℕ)) (mate : List ℕ) : List ℕ :=
  [a, b, σ, T.length] ++ T ++
    (List.range (a + b + 1)).map (fun v => ((nbrs.take v).map List.length).sum) ++
    mate ++ nbrs.flatten

/-- The output of Theorem 3.4 for the graph `localGraph a b nbrs` and the input matching `M`:
either `ws = [0]` (`⊥`) and every strong end has at least `σ` vertices, or `ws` lists a vertex set
`U` and the changes `D` of a matching `M′ = M ∆ D` of `G` with `|M′| ≥ |M|` such that `U` has at
least two vertices, is a source or sink SCC of `G_{M′}`, and `M′` fits `U`. -/
def LocalEndOutput (a b : ℕ) (nbrs : List (List ℕ)) (M : Finset ℕ) (σ : ℕ) (ws : List ℕ) :
    Prop :=
  (ws = [0] ∧ ∀ U, (localGraph a b nbrs).IsStrongEnd U → σ ≤ U.card) ∨
  ∃ (Ul : List ℕ) (Dl : List (ℕ × ℕ)),
    ws = [1, Ul.length] ++ Ul ++ [Dl.length] ++ Dl.flatMap (fun p => [p.1, p.2]) ∧
    Ul.Nodup ∧ Dl.Nodup ∧
    (∀ p ∈ Dl, p.1 < a ∧ p.2 < a + b ∧ p.1 * (a + b) + p.2 ∈ (localGraph a b nbrs).E) ∧
    let G := localGraph a b nbrs
    let M' := symmDiff M (Dl.map (fun p => p.1 * (a + b) + p.2)).toFinset
    let U := Ul.toFinset
    G.IsMatching M' ∧ M.card ≤ M'.card ∧ 2 ≤ U.card ∧
      (IsSourceSCC (G.altArc M') G.V U ∨ IsSinkSCC (G.altArc M') G.V U) ∧ G.Fits M' U

end Supplement

end BipDijoin


