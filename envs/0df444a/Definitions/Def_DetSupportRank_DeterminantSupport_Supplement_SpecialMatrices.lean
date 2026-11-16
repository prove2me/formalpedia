-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_SpecialMatrices
-- name    : DetSupportRank_DeterminantSupport_Supplement_SpecialMatrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:06:07.852136+00:00
-- url     : https://prove2.me/theorems/ff5b2dff-bb3d-4642-a093-0e7937db7878
-- title:
--   Dense and sparse alternating matrices and aligned subsets
-- statement:
--   Let $K_n$ have zero diagonal, entries one above the diagonal, and minus one below. Let $L_n$ be the direct sum of adjacent blocks $\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$ when $n$ is even. A subset $J$ is aligned precisely when it is a union of whole adjacent blocks:
--   $$J=\bigcup_{b\in B}\{2b,2b+1\},\qquad B\subseteq\{0,\ldots,n/2-1\}.$$
--   These are explicit matrices and subsets, without assuming their Pfaffian values. At order zero both matrices and the aligned empty union are included. A total odd-order sparse matrix has an unused zero last row and column; all statements about the whole matrix assume even order.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §4.2, dense matrix K_n and sparse matrix L_n, p. 11–12 (PDF p. 11–12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Mathlib

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Dense alternating matrix K_n on p.11. -/
def denseK (R : Type*) [Zero R] [One R] [Neg R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i < j then 1 else if j < i then -1 else 0

/-- Sparse alternating matrix L_n on p.12. Adjacent pairs are (0,1),(2,3),... . -/
def sparseL (R : Type*) [Zero R] [One R] [Neg R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i.val / 2 = j.val / 2 then denseK R n i j else 0

/-- One complete adjacent column block, with b ranging from 0 to n/2-1. -/
def adjacentBlock {n : ℕ} (b : Fin (n / 2)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j.val = 2 * b.val ∨ j.val = 2 * b.val + 1)

/-- A subset is a union of complete adjacent blocks, p.12. -/
def IsAligned {n : ℕ} (J : Finset (Fin n)) : Prop :=
  ∃ B : Finset (Fin (n / 2)), J = B.biUnion adjacentBlock
end DetSupportRank.DeterminantSupport.Supplement


