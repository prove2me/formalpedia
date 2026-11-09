-- Prove2me | Definitions.Def_HypClass1_maxCodeg
-- name    : HypClass1_maxCodeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:24:22.519961+00:00
-- url     : https://prove2.me/theorems/a7f276e2-ebb0-431c-a9ec-75d57d4cbc76
-- title:
--   Maximum codegree $\Delta_2(H)$
-- statement:
--   The **maximum codegree** of $H$ is
--   $$
--   \Delta_2(H) = \max_{u \ne v} \deg_H(u, v),
--   $$
--   the maximum over pairs of distinct vertices. A small maximum codegree is what nibble-type colouring results (Theorem 8.2) require.
--
--   **Formalization Note** The maximum is over ordered pairs of distinct vertices and is $0$ when there are fewer than two vertices.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.2

import Mathlib
import Definitions.Def_HypClass1_codeg

namespace HypClass1

/-- **Maximum codegree** `∆₂(H) = max_{u ≠ v} deg_H(u, v)`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.2: "let ∆₂(H) be the maximum
codegree of H, i.e., the maximum deg_H(u, v) for every u, v ∈ V(H)".

**Formalization Note.** The maximum ranges over ordered pairs of distinct vertices
(`Finset.offDiag`); it is `0` when there are fewer than two vertices. -/
def maxCodeg {V : Type*} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) : ℕ :=
  (Finset.univ : Finset V).offDiag.sup (fun uv => codeg H uv.1 uv.2)

end HypClass1


