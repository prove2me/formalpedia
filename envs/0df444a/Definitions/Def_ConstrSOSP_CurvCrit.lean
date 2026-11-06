-- Prove2me | Definitions.Def_ConstrSOSP_CurvCrit
-- name    : ConstrSOSP_CurvCrit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:05.379405+00:00
-- url     : https://prove2.me/theorems/4dad4121-d982-489e-8293-0448d51a4246
-- title:
--   Curvature criterion $\lambda_{\min}(\nabla^2f)<-\epsilon$
-- statement:
--   At $(x,y)$, $\lambda_{\min}(\nabla^2f(x,y))<-\epsilon$ (λ criterion), written through the Rayleigh quotient: some unit $v$ has $v^\top\nabla^2f(x,y)v<-\epsilon$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.4.1, p.32; (25), p.36

import Mathlib

namespace ConstrSOSP

/-- **The curvature criterion** (arXiv:2604.02285, 2 Nov 2026, §5.4.1, p.32: "λ < −ϵ0. (λ
criterion)", with `λ = λ_min(∇²f)`): at `(x, y)`, the Hessian of `f` has a Euclidean unit vector
`v = (v₁, v₂)` with `vᵀ∇²f v < −ε`, i.e. `λ_min(∇²f(x, y)) < −ε`.

**Formalization Note** `λ_min < −ε` is written through the Rayleigh quotient (the paper's (25),
p.36), with `f_xx`, `f_xy`, `f_yy` the iterated partial derivatives. -/
noncomputable def CurvCrit (f : ℝ → ℝ → ℝ) (ε x y : ℝ) : Prop :=
  ∃ v₁ v₂ : ℝ, v₁ ^ 2 + v₂ ^ 2 = 1 ∧
    v₁ ^ 2 * deriv (deriv (fun s => f s y)) x +
      2 * v₁ * v₂ * deriv (fun t => deriv (fun s => f s t) x) y +
      v₂ ^ 2 * deriv (deriv (fun t => f x t)) y < -ε

end ConstrSOSP


