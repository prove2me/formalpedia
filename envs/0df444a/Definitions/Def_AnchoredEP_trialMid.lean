-- Prove2me | Definitions.Def_AnchoredEP_trialMid
-- name    : AnchoredEP_trialMid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:39.938917+00:00
-- url     : https://prove2.me/theorems/3a9f5327-fa8b-4455-8f1f-da99a1d1ac9d
-- title:
--   Extrapolated trial point $z_{k+\frac12}(a)$
-- statement:
--   At the state $(z_k,v_k,A_k)$ with anchor $z_0$, the extrapolated point of the trial step $a$ is Eq. (10) with $a_k=a$:
--   $$
--   z_{k+\frac12}(a)=\frac{a}{A_k+a}z_0+\frac{A_k}{A_k+a}\big(z_k-a(F(z_k)+v_k)\big).
--   $$
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2, p.37, with Eq. (10), p.5

import Mathlib
import Definitions.Def_AnchoredEP_IterState

namespace AnchoredEP

/-- **The extrapolated point `z_{k+½}(a)` of a trial step.** Jiang–Yoon, arXiv:2609.30212,
Appendix G.2, p.37: "let `z_{k+½}(a)` be defined by (10) with `a_k = a`", where (10), p.5, is
`z_{k+½} = a_k/(A_k + a_k) z₀ + A_k/(A_k + a_k)(z_k − a_k(F(z_k) + v_k))`. -/
noncomputable def trialMid {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (a : ℝ) : EuclideanSpace ℝ (Fin d) :=
  (a / (s.A + a)) • z0 + (s.A / (s.A + a)) • (s.z - a • (F s.z + s.v))

end AnchoredEP


