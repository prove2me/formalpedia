-- Prove2me | Definitions.Def_TreeMultiflow_RatInstance_vertex
-- name    : TreeMultiflow_RatInstance_vertex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:54.347308+00:00
-- url     : https://prove2.me/theorems/8cdce6e8-b14e-4e42-9a74-19d290fca737
-- title:
--   Vertex with a given index in a rational instance
-- statement:
--   For an index $k$, the vertex $k$ of the vertex set $\{0,\dots,n\}$ of a rational instance.
--
--   **Formalization Note** The index is reduced modulo $n+1$; on well-formed instances all indices are at most $n$, so no reduction happens.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 1.2, p.3 (rationally encoded inputs)

import Mathlib
import Definitions.Def_TreeMultiflow_RatInstance

namespace TreeMultiflow

/-- **Vertex with a given index in a rational instance.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 1.2,
p.3 ("rationally encoded inputs").

`I.vertex k` is the vertex `k` of `Fin (I.n + 1)`.

**Formalization Note.** `Fin.ofNat` reduces `k` modulo `I.n + 1`; on well-formed instances every
index is at most `I.n` (`RatInstance.WellFormed`), so no reduction happens. -/
def RatInstance.vertex (I : RatInstance) (k : ℕ) : Fin (I.n + 1) :=
  Fin.ofNat (I.n + 1) k

end TreeMultiflow


