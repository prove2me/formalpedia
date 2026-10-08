-- Prove2me | Definitions.Def_TroppMatrixConcentration_dilation
-- name    : TroppMatrixConcentration_dilation
-- status  : Definition
-- author  : @tc
-- created : 2026-10-07T13:43:12.400981+00:00
-- url     : https://prove2.me/theorems/d7182f84-0e81-4a60-995c-79f27f7e895d
-- title:
--   Hermitian dilation of a rectangular matrix
-- statement:
--   For a complex matrix $A$ with arbitrary row and column index sets, its Hermitian dilation is the block matrix
--   $$H(A)=\begin{pmatrix}0&A\\A^*&0\end{pmatrix}.$$
--   The row and column index type of the result is the disjoint union of the original two index types. This definition supplies the rectangular-to-Hermitian construction used throughout the source.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Definition 2.1.5, equation (2.1.26), printed p. 24.

import Definitions.Def_TroppMatrixConcentration_spectral

namespace TroppMatrixConcentration

def dilation {m n : Type*} (A : Matrix m n ℂ) :
    Matrix (Sum m n) (Sum m n) ℂ := Matrix.fromBlocks 0 A A.conjTranspose 0

end TroppMatrixConcentration


