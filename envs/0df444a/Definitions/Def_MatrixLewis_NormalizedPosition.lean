-- Prove2me | Definitions.Def_MatrixLewis_NormalizedPosition
-- name    : MatrixLewis_NormalizedPosition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:29.499829+00:00
-- url     : https://prove2.me/theorems/f75f68fb-944a-4016-baaf-9adda0b03d49
-- title:
--   Normalized position $H_I(Z_I)=I_m$
-- statement:
--   Data $A_1,\dots,A_m$ are in **normalized position** if
--   $$
--   H_I(Z_I)=I_m ,
--   $$
--   where $H_I$ is their Gram map at the slack $I$ (so $B_i(I)=A_i$) and $Z_I$ is their maximizer at $I$. Then $M_*(I)=I_m$; Lemma 3.12 reduces every slack to this case.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), eq. (22), p.22

import Mathlib
import Definitions.Def_MatrixLewis_maximizer

namespace MatrixLewis

/-- Data `A₁, …, A_m` are in **normalized position** if `H_I(Z_I) = I_m` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), eq. (22),
p.22): their Gram matrix at the slack `I` (where `Bᵢ(I) = Aᵢ`) and their maximizer `Z_I` at `I`
is the identity. It depends on `q` through `Z_I`. -/
def NormalizedPosition {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  gram A 1 (maximizer q A 1) = 1

end MatrixLewis


