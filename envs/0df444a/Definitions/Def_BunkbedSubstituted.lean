-- Prove2me | Definitions.Def_BunkbedSubstituted
-- name    : BunkbedSubstituted
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-12T04:18:34.905637+00:00
-- url     : https://prove2.me/theorems/9d3182ec-d3cd-4467-8a31-46bb762244af
-- title:
--   The substituted graph of Theorem 1.2
-- statement:
--   Gladkov--Pak--Zimin obtain their counterexample to the bunkbed conjecture by **substituting** a copy of the gadget $G_n$, with $n = 3 \cdot 401 + 1 = 1204$, for each of the six $3$-hyperedges of Hollom's hypergraph. This file constructs that graph.
--
--   The gadget $G_n$ has vertex set $\{0, 1, \dots, n\}$: a hub $a = 0$ joined to every vertex of a path $v_1 - v_2 - \cdots - v_n$. Its three distinguished vertices are the hub and the two path ends. In the substitution, for each hyperedge $i$:
--
--   - the hub is identified with the hyperedge's **transversal** vertex $\texttt{hollomTr}\,i$;
--   - the two path ends $v_1$ and $v_n$ are identified with the hyperedge's two non-transversal vertices $\texttt{hollomPath}\,i$ and $\texttt{hollomPath}\,(i+1)$;
--   - the remaining $n - 2 = 1202$ path vertices are new, and private to that copy.
--
--   Since Hollom's hypergraph has ten vertices, the result has
--   $$10 + 6 \cdot 1202 \;=\; 7{,}222$$
--   vertices, and — the copies being edge-disjoint — $6 \cdot (2 \cdot 1204 - 1) = 14{,}442$ edges.
--
--   The carrier is $\mathrm{Fin}\,7222$, laid out concretely: the ten hypergraph vertices occupy $0, \dots, 9$, and the interior of copy $i$ occupies the block $10 + 1202i, \dots, 10 + 1202i + 1201$. The file provides the inclusion $\texttt{iota}$ of the ten hypergraph vertices, the per-copy vertex map $\texttt{emb}\,i$ realising the identifications above, the edge set $\texttt{subEdges}$ as the union of the six embedded gadget copies, and the transversal set $\texttt{subT}$ as the image of $\texttt{hollomT} = \{u_2, u_7, u_9\}$.
--
--   **Mathematical role.** This is the graph of Theorem 1.2. Because the six copies are edge-disjoint and meet only at the ten hypergraph vertices, percolation on it decomposes into independent percolation within each copy, and the only thing a copy contributes to global connectivity is the partition it induces on its three attachment vertices. That is what makes bunkbed percolation here a Wierman--Ziff model on Hollom's hypergraph, with the gadget's five partition probabilities as the state distribution — and hence what allows the robustness lemma to transfer Hollom's hypergraph counterexample to an honest graph.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Theorem 1.2 (p. 1), Figure 2 (p. 6) and Section 4.2 (p. 7).

import Definitions.Def_BunkbedWZSurgery

/-!
# The substituted graph of Theorem 1.2

Gladkov-Pak-Zimin obtain their counterexample by substituting a copy of the gadget `Gₙ` with
`n = 1204` for each of the six hyperedges of Hollom's hypergraph. The gadget's apex is identified
with the hyperedge's transversal vertex and its two path ends with the hyperedge's two
non-transversal vertices; the remaining `n - 2 = 1202` path vertices of each copy are new and
private to that copy. This yields `10 + 6 * 1202 = 7222` vertices and `6 * (2 * 1204 - 1) = 14442`
edges.

The ten hypergraph vertices sit at `0, …, 9` of `Fin 7222`, and the interior of copy `i` occupies
the block `10 + 1202 * i, …, 10 + 1202 * i + 1201`.
-/

namespace Bunkbed.Sub

open Bunkbed Bunkbed.Hyper SimpleGraph Finset

/-- The ten hypergraph vertices sit at `0, …, 9` of `Fin 7222`. -/
def iota (v : Fin 10) : Fin 7222 := ⟨v.val, by omega⟩

/-- The underlying index map of the copy glued in at hyperedge `i`: the gadget's apex `0` goes to
the transversal vertex, its path ends `1` and `1204` to the two non-transversal vertices, and its
interior to a private block. -/
def embN (i : Fin 6) (k : ℕ) : ℕ :=
  if k = 0 then (hollomTr i).val
  else if k = 1 then (hollomPath i.castSucc).val
  else if k = 1204 then (hollomPath i.succ).val
  else 10 + 1202 * i.val + (k - 2)

lemma embN_lt (i : Fin 6) (k : ℕ) (hk : k < 1205) : embN i k < 7222 := by
  have h1 : i.val < 6 := i.isLt
  have h3 : (hollomTr i).val < 10 := (hollomTr i).isLt
  have h4 : (hollomPath i.castSucc).val < 10 := (hollomPath i.castSucc).isLt
  have h5 : (hollomPath i.succ).val < 10 := (hollomPath i.succ).isLt
  unfold embN
  split_ifs <;> omega

/-- The vertex map of the copy of `G₁₂₀₄` glued in at hyperedge `i`. -/
def emb (i : Fin 6) (k : Fin 1205) : Fin 7222 := ⟨embN i k.val, embN_lt i k.val k.isLt⟩

/-- The edge set of the substituted graph: for each of the six hyperedges of Hollom's hypergraph,
a copy of `G₁₂₀₄` glued in along `emb i`. -/
def subEdges : Finset (Sym2 (Fin 7222)) :=
  Finset.univ.biUnion (fun i : Fin 6 => (gadgetE 1204).image (Sym2.map (emb i)))

/-- The transversal set of the substituted graph: the image of `hollomT = {u₂, u₇, u₉}`. -/
def subT : Finset (Fin 7222) := hollomT.image iota

end Bunkbed.Sub


