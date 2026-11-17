-- Prove2me | Definitions.Def_RandomLPIPM_Supplement_tilt
-- name    : RandomLPIPM_Supplement_tilt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:50:32.973071+00:00
-- url     : https://prove2.me/theorems/0904c202-4ee3-4b69-8cb2-2bf55b07fd9a
-- title:
--   The tilt $J_x(W)=\det(V^\top D_xV)$, $D_x=\mu X^{-2}$
-- statement:
--   For $x\in\mathbb R^n_{>0}$, $\mu>0$ and a $k$-dimensional subspace $W\subseteq\mathbb R^n$, let $D_x=\mu X^{-2}$ be the diagonal matrix with entries $\mu/x_i^2$ and $V$ any $n\times k$ matrix with orthonormal columns spanning $W$. The **tilt** is
--   $$J_x(W)=\det\big(V^\top D_x V\big).$$
--   It does not depend on the choice of $V$. In terms of the orthogonal projector $P_W$ onto $W$,
--   $$J_x(W)=\det\big(P_W D_x P_W+(I-P_W)\big).$$
--
--   The tilt is the density, up to normalisation, of the conditional law of the kernel of a Gaussian matrix given its central point with respect to the reference law on the fiber (Theorem 7.7).
--
--   **Formalization Note** The subspace is passed through its projector $P_W$, an $n\times n$ matrix. In the orthonormal basis $(V,U)$ of $\mathbb R^n=W\oplus W^\perp$ the matrix $P_WD_xP_W+(I-P_W)$ is block diagonal with blocks $V^\top D_xV$ and $I$, which gives the projector form.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), §7.3, p.64 (definition of J_x) and (104), p.65

import Mathlib

open Matrix

namespace RandomLPIPM.Supplement

/-- **The tilt `J_x(W) = det(VᵀD_xV)`, `D_x = μX⁻²`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), §7.3 p.64 and (104) p.65: for
`x ∈ ℝⁿ_{>0}` and `W ∈ Gr(k, n)`, `J_x(W) = det(VᵀD_xV)` with `D_x = μX⁻²` (diagonal, entries
`μ/xᵢ²`) and `V` any `n × k` matrix with orthonormal columns spanning `W`.

`tilt μ x P` takes `W` through its orthogonal projector `P = P_W` (an `n × n` matrix, given as a
function `Fin n → Fin n → ℝ`) and returns `det(P D_x P + (I − P))`.

**Formalization Note.** Basis-free form: with `V` an orthonormal basis of `W` and `U` one of `W^⊥`,
`P = VVᵀ` and `P D_x P + (I − P) = V(VᵀD_xV)Vᵀ + UUᵀ`, whose matrix in the orthonormal basis `(V, U)`
is `blockdiag(VᵀD_xV, I)`; so the determinant is `det(VᵀD_xV) = J_x(W)` for every projector `P`. -/
noncomputable def tilt {n : ℕ} (μ : ℝ) (x : Fin n → ℝ) (P : Fin n → Fin n → ℝ) : ℝ :=
  (Matrix.of P * diagonal (fun i => μ / x i ^ 2) * Matrix.of P + (1 - Matrix.of P)).det

end RandomLPIPM.Supplement


