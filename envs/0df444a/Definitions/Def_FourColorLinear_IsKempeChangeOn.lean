-- Prove2me | Definitions.Def_FourColorLinear_IsKempeChangeOn
-- name    : FourColorLinear_IsKempeChangeOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:01.629442+00:00
-- url     : https://prove2.me/theorems/042ebad8-b611-4afd-a722-e5cdd242a4ae
-- title:
--   Color pairings, Kempe edges, Kempe chains and Kempe changes on the colored part
-- statement:
--   Colors are $0,1,2,3$ (the paper's $1,2,3,4$). A **color pairing** splits them into two pairs $\{a,b\},\{c,d\}$; there are three. Let $W$ be the set of colored vertices and $\psi$ the coloring on it.
--
--   The **Kempe edges** for a pairing are the edges of $G$ inside $W$ joining the two colors of one pair. A **Kempe chain** is a component of the subgraph of $W$ formed by the Kempe edges; a vertex with no such edge is a chain alone. A **Kempe change** chooses a pairing and a union of chains, and swaps the two colors of the pair on it:
--   $$\psi'(v)=\begin{cases}\text{partner of }\psi(v)&v\text{ in a swapped chain},\\ \psi(v)&\text{otherwise,}\end{cases}\qquad v\in W.$$
--
--   Choosing no chain is allowed and leaves the coloring as it is. "Kempe chains and changes only apply to the colored vertices": the uncolored configurations play no part in them.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §1.1, p.2; §2.2, p.14

import Mathlib

namespace FourColorLinear

variable {V : Type}

/-- The partner of a color under one of the three color pairings of arXiv:2610.39753 (held version,
sha256 4dce39c5…), p.2 ("a color pairing {a, b} and {c, d} with {a, b, c, d} = {1, 2, 3, 4}"): the
color `0` is paired with `p + 1`. Colors `1, 2, 3, 4` of the paper are `0, 1, 2, 3` here. -/
def pairPartner (p : Fin 3) (c : Fin 4) : Fin 4 :=
  (![![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] : Fin 3 → Fin 4 → Fin 4) p c

/-- `ψ` is a proper coloring of the part of `G` on the vertex set `W`. -/
def ProperOn (G : SimpleGraph V) (W : Set V) (ψ : V → Fin 4) : Prop :=
  ∀ u v, u ∈ W → v ∈ W → G.Adj u v → ψ u ≠ ψ v

/-- The Kempe edges for pairing `p` (arXiv:2610.39753, p.14: "the ab- and cd-colored edges") in the
colored part `W`: "The Kempe chains only involve the colored vertices." -/
def kempeEdges (G : SimpleGraph V) (W : Set V) (ψ : V → Fin 4) (p : Fin 3) : Set (Sym2 V) :=
  {e | ∃ u v, e = s(u, v) ∧ G.Adj u v ∧ u ∈ W ∧ v ∈ W ∧ ψ v = pairPartner p (ψ u)}

/-- A Kempe chain (p.2): a component of the `ab`-colored or `cd`-colored subgraph of the colored
part. A vertex with no neighbour in its pair is a chain by itself. -/
def IsKempeChain (G : SimpleGraph V) (W : Set V) (ψ : V → Fin 4) (p : Fin 3) (K : Set V) : Prop :=
  ∃ v ∈ W, K = {u | u ∈ W ∧ (SimpleGraph.fromEdgeSet (kempeEdges G W ψ p)).Reachable v u}

/-- A Kempe change on the colored part `W` (arXiv:2610.39753, p.2): "we swap the colors on a subset
of the Kempe chains; that is, for an ab-colored component, a swap switches a and b, and on a
cd-colored component, it switches c and d."

**Formalization Note** `Sw` is the union of the swapped chains, i.e. a union of classes of the
chain relation; `Sw` empty is allowed and is the identity. Only values on `W` matter. -/
def IsKempeChangeOn (G : SimpleGraph V) (W : Set V) (ψ ψ' : V → Fin 4) : Prop :=
  ∃ (p : Fin 3) (Sw : Set V),
    (∀ u v, u ∈ W → v ∈ W → G.Adj u v → ψ v = pairPartner p (ψ u) → (u ∈ Sw ↔ v ∈ Sw)) ∧
      ∀ v ∈ W, (v ∈ Sw → ψ' v = pairPartner p (ψ v)) ∧ (v ∉ Sw → ψ' v = ψ v)

end FourColorLinear


