-- Prove2me | Definitions.Def_SparseDisc_relevantCoords
-- name    : SparseDisc_relevantCoords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:34.812109+00:00
-- url     : https://prove2.me/theorems/43e3124e-9cb4-4536-94bb-3d44708f6e71
-- title:
--   Coordinates relevant to a function on the cube
-- statement:
--   A coordinate $j$ is **relevant** to $g : \{\pm1\}^{\iota} \to \mathbb R$ if changing $x_j$ changes $g(x)$ for some $x$, i.e. $g(x) \ne g(x^{(j)})$ where $x^{(j)}$ is $x$ with coordinate $j$ flipped.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 2.1, p.11

import Mathlib
import Definitions.Def_SparseDisc_Cube

namespace SparseDisc

open Classical in
/-- The coordinates **relevant** to `g : {±1}^ι → ℝ`: those `j` such that changing `x_j` changes
`g(x)` for some `x` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), Section 2.1, p.11). -/
noncomputable def relevantCoords {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → ℝ) :
    Finset ι :=
  Finset.univ.filter (fun j => ∃ x : Cube ι, g x ≠ g (Function.update x j (-x j)))

end SparseDisc


