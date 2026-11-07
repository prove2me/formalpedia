-- Prove2me | Definitions.Def_PctDistortion_composition
-- name    : PctDistortion_composition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:16.309022+00:00
-- url     : https://prove2.me/theorems/2bcd707b-1e2e-42b9-9605-4062780f0202
-- title:
--   Composition and extension of digraphs; classes closed under extensions
-- statement:
--   Let $G=(V,E)$ be a digraph with $k=|V|$ nodes and let $H_1=(V_1,E_1),\dots,H_k=(V_k,E_k)$ be node-disjoint digraphs. The **composition** $G[H_1,\dots,H_k]$ replaces each vertex $i$ of $G$ by $H_i$: its nodes are $\bigcup_i V_i$ and its arcs are
--   $$\bigcup_{i=1}^k E_i\ \cup\ \{(u_i,v_j): u_i\in V_i,\ v_j\in V_j,\ (i,j)\in E\}.$$
--   When every $H_i$ is an independent set (no arcs), $G[H_1,\dots,H_k]$ is an **extension** of $G$. A class of digraphs is **closed under extensions** if every extension of a member is a member.
--
--   **Formalization Note** The node set is the disjoint union $\Sigma_i V_i$. An extension replaces vertex $i$ by $k_i\ge 1$ independent nodes (a digraph has at least one node). A class of digraphs is a predicate on digraphs over finite node types.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9

import Mathlib

set_option autoImplicit false

namespace PctDistortion

/-- The **composition** (substitution) `G[H₁, …, H_k]` of a digraph `G` on `I` with digraphs
`H_i` on node types `W i`: the nodes are the disjoint union `Σ i, W i` (block `i` is `W i`),
and the arcs are the arcs of each `H_i` inside block `i` together with every `(u_i, v_j)`,
`u_i ∈ V_i`, `v_j ∈ V_j`, for which `(i, j)` is an arc of `G`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9: "the composition G[H1, H2, . . . , Hk] (also called substitution) is obtained by
replacing each vertex i of G with the digraph Hi. More precisely, the nodes are ⋃_{i=1}^k Vi, and
the arcs are ⋃_{i=1}^k Ei ∪ {(ui, vj) | ui ∈ Vi, vj ∈ Vj, (i, j) ∈ E}." -/
def composition {I : Type} (G : Digraph I) {W : I → Type} (H : ∀ i, Digraph (W i)) :
    Digraph (Σ i, W i) where
  Adj x y := (∃ (i : I) (u u' : W i), x = ⟨i, u⟩ ∧ y = ⟨i, u'⟩ ∧ (H i).Adj u u') ∨ G.Adj x.1 y.1

/-- The **extension** of `G` replacing each vertex `i` by an independent set of `k i` nodes:
the composition `G[H₁, …, H_k]` in which every `H_i` is the arcless digraph on `Fin (k i)`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9: "For the specific case when each of the Hi is an independent set (i.e., they do not
contain any arcs), G[H1, H2, . . . , Hk] is called an extension of G." -/
def extension {I : Type} (G : Digraph I) (k : I → ℕ) : Digraph (Σ i, Fin (k i)) :=
  composition G (fun i => Digraph.emptyDigraph (Fin (k i)))

/-- A **class of digraphs**: a predicate on digraphs over finite node types. -/
abbrev DigraphClass : Type 1 := ∀ (W : Type) [Fintype W], Digraph W → Prop

/-- A class of digraphs is **closed under extensions**: every extension of a member, with every
vertex replaced by a nonempty independent set, is again a member.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9: "It is closed under extension if for every digraph G ∈ H, all extensions of G are
also in H."

**Formalization Note.** Each independent set has `k i ≥ 1` nodes: a digraph has at least one
node, and every member of the classes used in the paper (`M_α`) is nonempty. -/
def ClosedUnderExtensions (𝓗 : DigraphClass) : Prop :=
  ∀ (I : Type) [Fintype I] (G : Digraph I) (k : I → ℕ), (∀ i, 1 ≤ k i) → 𝓗 I G →
    𝓗 (Σ i, Fin (k i)) (extension G k)

end PctDistortion


