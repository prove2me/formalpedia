-- Prove2me | Definitions.Def_SpencerEight_Supplement_Letter
-- name    : SpencerEight_Supplement_Letter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:49:19.008196+00:00
-- url     : https://prove2.me/theorems/727d4bc9-3f8d-4620-9f37-1eb284d88e95
-- title:
--   The letters $I, X, Z, J$
-- statement:
--   The four letters of Section 15.2 are the real $2\times2$ matrices
--   $$
--   I=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
--   $$
--   $I,X,Z$ are symmetric; $J$ is antisymmetric with $J^2=-I$.
--
--   **Formalization Note** An inductive type of four letters together with its matrix map `Letter.mat`.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 15.2, p.289 (PDF p.289)

import Mathlib

namespace SpencerEight.Supplement

/-- The four letters `I, X, Z, J` of Section 15.2 (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.289 (PDF p.289)). -/
inductive Letter where
  | I
  | X
  | Z
  | J
  deriving DecidableEq

/-- The `2 × 2` real matrix of a letter (Section 15.2, p.289):
`I = [[1,0],[0,1]]`, `X = [[0,1],[1,0]]`, `Z = [[1,0],[0,−1]]`, `J = [[0,1],[−1,0]]`
(`J` is antisymmetric, `J² = −I`). -/
def Letter.mat : Letter → Matrix (Fin 2) (Fin 2) ℝ
  | .I => !![1, 0; 0, 1]
  | .X => !![0, 1; 1, 0]
  | .Z => !![1, 0; 0, -1]
  | .J => !![0, 1; -1, 0]

end SpencerEight.Supplement


