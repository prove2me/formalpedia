-- Prove2me | Definitions.Def_PassivityUn_stdJ
-- name    : PassivityUn_stdJ
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-23T20:52:37.314291+00:00
-- url     : https://prove2.me/theorems/33b8a928-7d85-4ce9-bc3a-e70e1d559b13
-- title:
--   Standard complex structure $J = \begin{pmatrix} 0 & -I \\ I & 0 \end{pmatrix}$
-- statement:
--   For a natural number $n$, let $\mathrm{Blk}(n)$ be the disjoint union of two copies of $\{0,\dots,n-1\}$. Real matrices indexed by $\mathrm{Blk}(n)$ are the real $2n\times 2n$ matrices written in $2\times 2$ block form with $n\times n$ blocks, the first copy indexing the upper/left blocks.
--
--   The **standard complex structure** is the block matrix
--
--   $$
--   J_n = \begin{pmatrix} 0 & -I_n \\ I_n & 0 \end{pmatrix},
--   $$
--
--   where $I_n$ is the $n\times n$ identity matrix.
--
--   This is the fixed matrix against which "respecting the complex structure" is measured throughout the mission; it satisfies $J_n^2 = -1$ (milestone M1).
--
--   **Formalization Note** $\mathrm{Blk}(n)$ is `Fin n ⊕ Fin n`, and $J_n$ is `Matrix.fromBlocks 0 (-1) 1 0`.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1 (complex structure J): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(b): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib

open Matrix

namespace PassivityUn

/-- Index type for 2n × 2n matrices in 2 × 2 block form. -/
abbrev Blk (n : ℕ) := Fin n ⊕ Fin n

/-- The standard complex structure J = [[0, -I], [I, 0]]. -/
def stdJ (n : ℕ) : Matrix (Blk n) (Blk n) ℝ :=
  Matrix.fromBlocks 0 (-1) 1 0

end PassivityUn


