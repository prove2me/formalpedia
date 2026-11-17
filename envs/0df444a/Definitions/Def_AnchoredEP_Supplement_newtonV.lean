-- Prove2me | Definitions.Def_AnchoredEP_Supplement_newtonV
-- name    : AnchoredEP_Supplement_newtonV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:04:27.497948+00:00
-- url     : https://prove2.me/theorems/8ca221da-444c-4865-bda9-273df8744f39
-- title:
--   Trial vector $v_{k+1}(a)$ of AEP Newton
-- statement:
--   At an outer iteration $k$ of the AEP Newton method with state $(z_k,v_k,A_k)$ and a trial step $a>0$, let $z_{k+\frac12}(a)$ be the extrapolated point (10) and $z_{k+1}(a)$ the solution of the affine-model subproblem (49). The associated **trial vector** is
--   $$
--   v_{k+1}(a):=\frac1a\Big(\frac{a}{A_k+a}z_0+\frac{A_k}{A_k+a}z_k-z_{k+1}(a)\Big)-\Big(F(z_{k+\frac12}(a))+DF(z_{k+\frac12}(a))\big(z_{k+1}(a)-z_{k+\frac12}(a)\big)\Big).
--   $$
--   By (49), $v_{k+1}(a)\in H(z_{k+1}(a))$, so $\|F(z_{k+1}(a))+v_{k+1}(a)\|$ is a computable upper bound on the tangent residual of the trial point. Algorithm 1 uses it as the next vector $v_{k+1}$.
--
--   **Formalization Note** $z_{k+1}(a)$ is the published `trialZ F sol z0 s a`, the solver output at the extrapolated and anchored points.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Eq. (50), p.25; Algorithm 1 line 10, p.8

import Mathlib
import Definitions.Def_AnchoredEP_taylorOp
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_trialAnchor
import Definitions.Def_AnchoredEP_trialMid
import Definitions.Def_AnchoredEP_trialZ

namespace AnchoredEP.Supplement

/-- **The trial vector `v_{k+1}(a)` of AEP Newton.** Jiang–Yoon, arXiv:2609.30212, Eq. (50), p.25
(also Algorithm 1 line 10, p.8):
`v_{k+1}(a) := (1/a)(a/(A_k + a) z₀ + A_k/(A_k + a) z_k − z_{k+1}(a)) − P_{k,a}(z_{k+1}(a))`,
with the affine model `P_{k,a}(z) = F(z_{k+½}(a)) + DF(z_{k+½}(a))(z − z_{k+½}(a))`.

**Formalization Note.** `z_{k+1}(a)` is the published `trialZ F sol z0 s a`
(`= sol a (z_{k+½}(a)) (anchored point)`); with a solver satisfying `IsNewtonSolver` it is the
solution of (49). The affine model is `taylorOp F 2`. -/
noncomputable def newtonV {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (a : ℝ) : EuclideanSpace ℝ (Fin d) :=
  a⁻¹ • (trialAnchor z0 s a - trialZ F sol z0 s a)
    - taylorOp F 2 (trialMid F z0 s a) (trialZ F sol z0 s a)

end AnchoredEP.Supplement


