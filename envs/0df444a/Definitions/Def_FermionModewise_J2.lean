-- Prove2me | Definitions.Def_FermionModewise_J2
-- name    : FermionModewise_J2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:24.408377+00:00
-- url     : https://prove2.me/theorems/94a2a362-457e-46f4-a6d0-7e08718ce95d
-- title:
--   The matrix $J_2$
-- statement:
--   The real $2\times2$ matrix
--   $$J_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.$$
--   It satisfies $J_2^2=-\mathbb 1_2$ and is the building block of the fermion Williamson form (9). The covariance matrix of the vacuum of one mode is $J_2$.
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (9), p.5

import Mathlib

open Matrix

namespace FermionModewise

/-- The `2 × 2` matrix `J₂ = [[0, −1], [1, 0]]` (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (9),
p.5). -/
def J2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

end FermionModewise


