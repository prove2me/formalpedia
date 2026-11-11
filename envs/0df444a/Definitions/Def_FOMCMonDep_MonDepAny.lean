-- Prove2me | Definitions.Def_FOMCMonDep_MonDepAny
-- name    : FOMCMonDep_MonDepAny
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:45.692274+00:00
-- url     : https://prove2.me/theorems/3d5cf4fe-aa12-4f83-b168-9ea1da59eb1e
-- title:
--   Monadic dependence for classes of possibly infinite graphs
-- statement:
--   A graph class $\mathcal C$ is **monadically independent** if there are $k\in\mathbb N$ and a first-order formula $\varphi(x,y)$ in the signature of $k$-colored graphs such that every finite graph $H$ is isomorphic to an induced subgraph of $\varphi(G^+)$ for some $G\in\mathcal C$ and some $k$-coloring $G^+$ of $G$; here $\varphi(G^+)$ has vertex set $V(G)$ and edges $uv$ with $G^+\models\varphi(u,v)\vee\varphi(v,u)$. The class is **monadically dependent** if it is not monadically independent.
--
--   In Part I of the paper the graphs of a class may be infinite. This item defines graph classes whose members live on arbitrary vertex types, and monadic dependence for them, with the same formula as the published finite-graph notion `MonDepMW.MonadicallyDependent`.
--
--   **Formalization Note** A class is given by its members on each vertex type $V$. The witness graph $G$ may be on any type; $H$ ranges over the graphs on $\{0,\dots,m-1\}$, which represent all finite graphs. For a class of finite graphs closed under isomorphic copies this is the published notion.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §3, p.11 (PDF 13); Part I, p.17 (PDF 19)

import Mathlib
import Definitions.Def_MonDepMW_MonadicallyDependent

set_option autoImplicit false

namespace FOMCMonDep

/-- **Graph classes of possibly infinite graphs** (Part I). Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), p.17 (PDF 19): "all
considered graphs may be finite or infinite in Part I". A class is given by its members on each vertex type
`V : Type`.

**Formalization Note.** No closure under isomorphism is assumed; the notions of this mission are isomorphism
invariant. The published `MonDepMW.GraphClass` is the finite-graph version (members on each `Fin n`) used from
Lemma 4.10 on. -/
abbrev AnyGraphClass := ∀ V : Type, Set (SimpleGraph V)

/-- **Monadic dependence for classes of possibly infinite graphs.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, p.11
(PDF 13): "A graph class 𝒞 is monadically independent if there are k ∈ N and a first-order formula φ(x, y) in the
signature of k-colored graphs such that every finite graph H can be obtained from some graph G ∈ 𝒞 as follows: first
choose a k-coloring G⁺ of G, then consider the graph φ(G⁺) with vertex set V(G) and edges uv ∈ (V(G) choose 2) such
that G⁺ |= φ(u, v) ∨ φ(v, u); finally take some induced subgraph of φ(G⁺), obtaining a graph isomorphic to H. A graph
class 𝒞 is monadically dependent if it is not monadically independent."

**Formalization Note.** The same formula as the published `MonDepMW.MonadicallyDependent`, with the witness graph
`G` on any vertex type. `H ↪g φ(G⁺)` (an embedding preserving and reflecting adjacency) is "an induced subgraph of
φ(G⁺) isomorphic to H"; every finite graph has a copy on some `Fin m`. For a class of finite graphs, closed under
isomorphic copies on every type, this coincides with `MonDepMW.MonadicallyDependent` of its `Fin n` members. -/
def MonDepAny (𝒞 : AnyGraphClass) : Prop :=
  ¬ ∃ (k : ℕ) (φ : (MonDepMW.coloredGraph k).Formula (Fin 2)), ∀ (m : ℕ) (H : SimpleGraph (Fin m)),
      ∃ (V : Type) (G : SimpleGraph V) (c : Fin k → Set V), G ∈ 𝒞 V ∧ Nonempty (H ↪g MonDepMW.interp φ G c)

end FOMCMonDep


