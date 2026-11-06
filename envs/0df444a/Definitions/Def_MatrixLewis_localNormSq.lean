-- Prove2me | Definitions.Def_MatrixLewis_localNormSq
-- name    : MatrixLewis_localNormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:14:00.399534+00:00
-- url     : https://prove2.me/theorems/fecd3c46-bb65-42d2-a069-60e02e905949
-- title:
--   Squared local norm $Q_S(\dot S)$ and Lewis metric $M_x$
-- statement:
--   For $S\succ0$ and $\dot S\in\mathbb S^n$, put $X=S^{-1/2}\dot SS^{-1/2}$. The **squared local norm** and, for $x\in\mathcal D$, the **Lewis metric** are
--   $$
--   Q_S(\dot S):=\operatorname{tr}(X\Lambda_SX),\qquad (M_x)_{ij}:=\operatorname{tr}\bigl(B_i(S_x)\Lambda_{S_x}B_j(S_x)\bigr),
--   $$
--   so that $h^\top M_xh=Q_{S_x}(\mathcal Ah)$. $Q_S$ is the squared local norm $\operatorname{tr}(X^2)$ of the log-determinant barrier with $I_n$ replaced by $\Lambda_S$.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.14, p.24, eqs. (27)–(28)

import Mathlib
import Definitions.Def_MatrixLewis_lewisWeight
import Definitions.Def_MatrixLewis_slack

namespace MatrixLewis

/-- The squared local norm `Q_S(Ṡ) := tr(X Λ_S X)` with `X = S^{−1/2} Ṡ S^{−1/2}` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…),
Definition 3.14, p.24, eq. (27)). -/
noncomputable def localNormSq {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S Sdot : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  let X := mpow (-(1 / 2 : ℝ)) S * Sdot * mpow (-(1 / 2 : ℝ)) S
  (X * lewisWeight q A S * X).trace

/-- The Lewis metric `(M_x)ᵢⱼ := tr(Bᵢ(S_x) Λ_{S_x} Bⱼ(S_x))` at `x ∈ 𝒟` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…),
Definition 3.14, p.24). -/
noncomputable def lewisMetric {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin m)) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    (scaled A (slack A C x) i * lewisWeight q A (slack A C x) * scaled A (slack A C x) j).trace

end MatrixLewis


