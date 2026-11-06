-- Prove2me | Definitions.Def_RollingProbeQN_Convex_modelStep
-- name    : RollingProbeQN_Convex_modelStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:02.129226+00:00
-- url     : https://prove2.me/theorems/2de30103-a67f-4377-8a4f-62bdfc20197c
-- title:
--   The regularized model step $r=-(B+\lambda^{-1}I)^{-1}v$
-- statement:
--   For a matrix $B$, a stepsize $\lambda>0$ and a vector $v$,
--
--   $$r=-(B+\lambda^{-1}I)^{-1}v .$$
--
--   With $v=\nabla f(y_k)$ this is the quasi-Newton step of Algorithm 1, the solution of $(B_k+\lambda_k^{-1}I)r_k=-\nabla f(y_k)$.
--
--   **Formalization Note** The matrix acts on $\mathbb R^d$ through `Matrix.toEuclideanLin`; for $B\succeq0$ and $\lambda>0$ the matrix $B+\lambda^{-1}I$ is invertible.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, §2.2, p. 8; Algorithm 1, Step 3, p. 9

import Mathlib

namespace RollingProbeQN.Convex

/-- **The regularized model step `r = −(B + λ⁻¹I)⁻¹ v`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §2.2, p. 8: "take `r = −(B + λ^{−1}I)^{−1}∇F(y)`"; Algorithm 1, Step 3, p. 9: "solve
`(B_k + λ_k^{−1} I) r_k = −∇f(y_k)`".

`modelStep B λ v = −(B + λ⁻¹ I)⁻¹ v`, the matrix acting on `ℝ^d` through `Matrix.toEuclideanLin`.

**Formalization Note.** `⁻¹` is the matrix inverse; for `B ⪰ 0` and `λ > 0` the matrix
`B + λ⁻¹ I` is invertible, which is the only case the mission uses. -/
noncomputable def modelStep {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  -(Matrix.toEuclideanLin (B + lam⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ v)

end RollingProbeQN.Convex


