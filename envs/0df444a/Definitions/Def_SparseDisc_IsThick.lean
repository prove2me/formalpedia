-- Prove2me | Definitions.Def_SparseDisc_IsThick
-- name    : SparseDisc_IsThick
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:54:10.764636+00:00
-- url     : https://prove2.me/theorems/dcd897ea-33b7-499c-8e63-2cacc4039628
-- title:
--   Thick subset of the cube
-- statement:
--   A set $B \subseteq \{\pm1\}^S$ is **thick** if every antipodal 1-path in $\{\pm1\}^S$ meets $B$, that is, if $\{\pm1\}^S \setminus B$ contains no 1-loop. Equivalently, every path along the edges of the cube from a vertex $z$ to its antipode $-z$ meets $B$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 8.4, p.33; Section 1.1, p.5

import Mathlib
import Definitions.Def_SparseDisc_HasLoop

namespace SparseDisc

/-- `IsThick B`: `B ⊆ {±1}^U` is **thick** — every antipodal 1-path meets `B`, i.e. the complement
of `B` contains no 1-loop (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*,
STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Section 8.4, p.33; also p.5). -/
def IsThick {U : Type} [Fintype U] (B : Set (Cube U)) : Prop := ¬ HasLoop 1 Bᶜ

end SparseDisc


