-- Prove2me | Definitions.Def_SparseDisc_IsCactus
-- name    : SparseDisc_IsCactus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:29.736345+00:00
-- url     : https://prove2.me/theorems/a46490fc-bcd8-4d8a-b707-b2b06ad30261
-- title:
--   Cactus graph
-- statement:
--   A graph $H$ is a **cactus** if every block of $H$ is an edge or a cycle.
--
--   **Formalization Note** No connectivity of $H$ is required, as in the paper; blocks are those of `SparseDisc.IsBlock`.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 1.1, p.4: 'a cactus (every block is an edge or a cycle)'

import Mathlib
import Definitions.Def_SparseDisc_IsBlock
import Definitions.Def_SparseDisc_IsCycle

namespace SparseDisc

/-- `IsCactus H`: `H` is a **cactus** — every block is an edge or a cycle (Zeng–Cao–Dai–Wang–Liao,
*Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission manuscript (sha256
0f09ec60…25b81), p.4: "a cactus (every block is an edge or a cycle)").

**Formalization Note** No connectivity of `H` is required (the paper requires none); blocks are as
in `IsBlock`. -/
def IsCactus {V : Type} [DecidableEq V] (H : SimpleGraph V) : Prop :=
  ∀ W : Finset V, IsBlock H W → W.card = 2 ∨ IsCycle (H.induce (W : Set V))

end SparseDisc


