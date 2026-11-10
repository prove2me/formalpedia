-- Prove2me | Definitions.Def_RandTreeUniv_IsUniversal
-- name    : RandTreeUniv_IsUniversal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:17.135528+00:00
-- url     : https://prove2.me/theorems/64058fb8-35fc-4c66-8422-c36c0197a93a
-- title:
--   $\mathcal F$-universal graph
-- statement:
--   A graph $G$ is **universal** for a family of graphs $\mathcal F$ (or $\mathcal F$-universal) if it contains an isomorphic copy of every graph of $\mathcal F$ as a subgraph: for every $T\in\mathcal F$ there is an injective map $\varphi:V(T)\to V(G)$ such that $\varphi(u)\varphi(v)$ is an edge of $G$ whenever $uv$ is an edge of $T$.
--
--   The copy need not be induced: $G$ may have additional edges among the image vertices. All members of $\mathcal F$ must embed into the same graph $G$; in a random graph this means one event containing all of them, not one event per member.
--
--   **Formalization Note** $\mathcal F$ is a predicate on graphs with the same vertex set as $G$; copies are Mathlib's `SimpleGraph.IsContained`.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §1, p.1 (PDF 2)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `G` is `F`-universal (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §1, p.1 (PDF 2)): "A graph `G` is said to be universal
for a family of graphs `F` … if it contains an isomorphic copy of every graph in `F` as a
subgraph."

**Formalization Note** The family is a predicate on graphs with the vertex set of `G` (for
families of `n`-vertex graphs and `G` on `Fin n`). A copy as a subgraph is
`SimpleGraph.IsContained` (an injective vertex map sending edges to edges, not necessarily
induced). -/
def IsUniversal {V : Type*} (G : SimpleGraph V) (F : SimpleGraph V → Prop) : Prop :=
  ∀ T, F T → T.IsContained G

end RandTreeUniv


