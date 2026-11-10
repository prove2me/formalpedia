-- Prove2me | Definitions.Def_PPSLattice_decMat
-- name    : PPSLattice_decMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:34:30.137093+00:00
-- url     : https://prove2.me/theorems/9e373fdb-79ca-479f-bf44-5f2e15f0ab7f
-- title:
--   Parser of a matrix in $\mathbb Z_q^{a\times b}$
-- statement:
--   The inverse of the matrix code: entry $(i,j)$ of the parsed matrix is block $ib+j$ of $\lceil\log q\rceil$ bits, read in binary and reduced modulo $q$.
--
--   Figure 1 parses its input $b\in\{0,1\}^{nm\lceil\log q\rceil}$ as $\mathbf B\in\mathbb Z_q^{n\times m}$ this way, and the algorithms of Construction 4.6 read $\mathbf A$ from $\mathrm{crs}$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Figure 1, p.22; Construction 4.6, p.21

import Mathlib
import Definitions.Def_PPSLattice_decVec
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **parser of an `a × b` matrix over Z_q** in the row-major layout of `encMat`: entry
`(i, j)` is block `i · b + j` of `⌈log₂ q⌉` bits.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Figure 1, p.22 ("Parse input b as B ∈ Z_q^{n×m}") and Construction 4.6, p.21
(algorithms read A from crs). -/
def decMat (q a b : ℕ) (w : Str) : Matrix (Fin a) (Fin b) (ZMod q) :=
  Matrix.of fun i j => decVec q (Nat.clog 2 q) (a * b) w (finProdFinEquiv (i, j))

end PPSLattice


