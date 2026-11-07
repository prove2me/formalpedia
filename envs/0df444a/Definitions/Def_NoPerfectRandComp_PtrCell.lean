-- Prove2me | Definitions.Def_NoPerfectRandComp_PtrCell
-- name    : NoPerfectRandComp_PtrCell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:22.483372+00:00
-- url     : https://prove2.me/theorems/e72a04d8-17df-4bbd-9072-bea388353cb7
-- title:
--   Pointer-cell alphabet $A_q=\{0,1\}\times([q]\cup\{\bot\})^{[q]}\times([q]\cup\{\bot\})$
-- statement:
--   A **pointer cell** is an element of the finite alphabet
--   $$
--   A_q = \{0,1\} \times ([q]\cup\{\bot\})^{[q]} \times ([q]\cup\{\bot\}) .
--   $$
--   Its components are a value bit $v$, row pointers $\mathrm{row}_j$ for $j\in[q]$, and a column pointer $\mathrm{col}$.
--
--   **Formalization Note** $[q]$ is `Fin q` (0-based) and $\bot$ is `none`.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §5.1, p.18

import Mathlib

namespace NoPerfectRandComp

/-- A pointer cell (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §5.1, p.18): an element of
`A_q = {0,1} × ([q] ∪ {⊥})^{[q]} × ([q] ∪ {⊥})`, i.e. a value bit `v` (first component), row
pointers `row_j` for `j ∈ [q]` (second component) and a column pointer `col` (third component).
`⊥` is `none` and `[q]` is `Fin q` (0-based). -/
abbrev PtrCell (q : ℕ) : Type := Bool × (Fin q → Option (Fin q)) × Option (Fin q)

end NoPerfectRandComp


