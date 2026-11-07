-- Prove2me | Definitions.Def_SparseDisc_IsOdd
-- name    : SparseDisc_IsOdd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:26.232695+00:00
-- url     : https://prove2.me/theorems/0b77f207-0b21-4e1a-aa1d-d379a4b62744
-- title:
--   Odd function on the cube
-- statement:
--   A function $g : \{\pm1\}^U \to \mathbb R$ is **odd** if $g(-z) = -g(z)$ for every $z$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 2 (Notation), p.11

import Mathlib
import Definitions.Def_SparseDisc_Cube

namespace SparseDisc

/-- A function `g : {±1}^U → ℝ` is **odd**: `g(−z) = −g(z)` (Zeng–Cao–Dai–Wang–Liao, *Sparse
Discrepancy Beyond Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81),
Section 2, p.11). -/
def IsOdd {U : Type} (g : Cube U → ℝ) : Prop := ∀ z, g (-z) = -g z

end SparseDisc


