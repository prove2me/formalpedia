-- Prove2me | Definitions.Def_ExitSpirals_Network
-- name    : ExitSpirals_Network
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:19.301+00:00
-- url     : https://prove2.me/theorems/2f595062-43cf-42e6-beaf-8e6972aa575b
-- title:
--   Directed networks on $n$ agents: links, in- and out-degrees, stripped network $G(W)$
-- statement:
--   There are $n$ agents $N=\{1,\dots,n\}$. A **directed network** $G$ is a set $E$ of ordered pairs of agents; the link $j\to i$ means that $j$ supports $i$'s activity. The network is **loopless** when it contains no link $i\to i$ (the paper assumes this throughout).
--
--   1. The **in-degree** $d^-_i$ of agent $i$ is the number of links $j\to i$; the **out-degree** $d^+_i$ is the number of links $i\to j$.
--   2. For a set $W$ of agents, the **stripped network** $G(W)$ keeps exactly the links neither of whose endpoints lies in $W$: all edges of the agents in $W$ are removed.
--
--   These are the objects on which the two markets $R$ and $C$ are built; $G_R(W)$ and $G_C(W)$ are the networks after the shocked agents $W$ have withdrawn.
--
--   **Formalization Note** Agents are `Fin n`; a network is a `Finset (Fin n × Fin n)`, so multiple links do not occur (the paper's random networks are simple graphs). The pair `(j, i)` is the link $j\to i$. Looplessness is the separate predicate `IsLoopless`.
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), §2.1 and Definition 2.1, pp.7–8 (networks, no self-links, in-/out-neighbourhoods); §4.2, p.23 (G(W))

import Mathlib

namespace ExitSpirals

/-- **A directed network on the agents `Fin n`.**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, §2.1, p.7:
"A directed network G is a set of nodes V(G) together with a set E(G) of directed links, i.e.,
ordered pairs (i, j) with i, j ∈ N. … We write i → j for a link from i to j in market µ, which we
interpret as any interaction that supports j's activity."

A network is the finite set `E` of its links; the pair `(j, i) ∈ E` is the link `j → i`, so `j`
supports `i`.

**Formalization Note.** Agents are `Fin n` (the paper's `N = {1, …, n}`). A network is a
`Finset` of ordered pairs, so there are no multiple links (A.3, p.47, conditions on simple graphs).
The paper's standing assumption "there are no self-links" (p.7) is the separate predicate
`IsLoopless`, assumed wherever the paper assumes it. -/
abbrev Network (n : ℕ) : Type := Finset (Fin n × Fin n)

/-- No self-links (§2.1, p.7, footnote 7: "for all networks we consider, (i, i) ∉ E(G)"). -/
def IsLoopless {n : ℕ} (E : Network n) : Prop := ∀ e ∈ E, e.1 ≠ e.2

/-- In-degree `d⁻_i = |K⁻_i|`, the number of links `j → i` (Definition 2.1, p.7). -/
def inDeg {n : ℕ} (E : Network n) (i : Fin n) : ℕ := (E.filter fun e => e.2 = i).card

/-- Out-degree `d⁺_i`, the number of links `i → j` (p.8). -/
def outDeg {n : ℕ} (E : Network n) (i : Fin n) : ℕ := (E.filter fun e => e.1 = i).card

/-- The stripped network `G(W)` (p.23): "the networks after all the edges corresponding to the
agents in W … have been removed". A link is kept iff neither endpoint is in `W`. -/
def strip {n : ℕ} (E : Network n) (W : Finset (Fin n)) : Network n :=
  E.filter fun e => e.1 ∉ W ∧ e.2 ∉ W

end ExitSpirals


