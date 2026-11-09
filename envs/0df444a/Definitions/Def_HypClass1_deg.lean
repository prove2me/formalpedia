-- Prove2me | Definitions.Def_HypClass1_deg
-- name    : HypClass1_deg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:45.210769+00:00
-- url     : https://prove2.me/theorems/f754c3ef-67e0-4328-9975-3d444fa94059
-- title:
--   Vertex degree $\deg_H(x)$
-- statement:
--   For a set $H$ of edges and a vertex $x$, the **degree** of $x$ is the number of edges containing it,
--   $$
--   \deg_H(x) = |\{e \in H : x \in e\}|.
--   $$
--   All edges incident to $x$ must receive distinct colours in a proper edge-colouring, which is the source of the lower bound $\chi'(H) \ge \Delta(H)$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.1

import Mathlib

namespace HypClass1

/-- **Vertex degree** `deg_H(x)`: the number of edges of `H` containing the vertex `x`.
Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.1 and throughout.

**Formalization Note.** `H` is any finite set of finite vertex sets (in the mission, a 3-graph,
i.e. a subset of `K3 V`). -/
def deg {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (x : V) : ℕ :=
  (H.filter (fun e => x ∈ e)).card

end HypClass1


