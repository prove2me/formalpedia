-- Prove2me | Definitions.Def_SparseDisc_IsNearThick
-- name    : SparseDisc_IsNearThick
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:54:26.919473+00:00
-- url     : https://prove2.me/theorems/9fcc6b00-3c60-4bce-93d3-ba77d468d2fa
-- title:
--   Near-thick subset of the cube
-- statement:
--   A set $\Omega \subseteq \{\pm1\}^S$ is **near-thick** if $\{\pm1\}^S \setminus \Omega$ contains no near-loop.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 8.7, pp.39–40

import Mathlib
import Definitions.Def_SparseDisc_HasNearLoop

namespace SparseDisc

/-- `IsNearThick Ω`: `Ω ⊆ {±1}^U` is **near-thick** — its complement contains no near-loop
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Section 8.7, p.39). -/
def IsNearThick {U : Type} [Fintype U] (Ω : Set (Cube U)) : Prop := ¬ HasNearLoop Ωᶜ

end SparseDisc


