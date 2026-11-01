-- Prove2me | Definitions.Def_MarkovSA_IsSmoothNorm
-- name    : MarkovSA_IsSmoothNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:09.010654+00:00
-- url     : https://prove2.me/theorems/55274ae6-28f9-4a40-8015-5919b345aa78
-- title:
--   The smoothing norm $\|\cdot\|_s$: $g=\tfrac12\|\cdot\|_s^2$ is convex and $L$-smooth
-- statement:
--   A function $\|\cdot\|_s$ on $E$ is an **$L$-smooth norm** ($L>0$) if it satisfies the norm axioms and $g(x)=\frac12\|x\|_s^2$ is convex, differentiable and
--
--   $$
--   g(x_2)\le g(x_1)+\langle\nabla g(x_1),x_2-x_1\rangle+\frac L2\|x_1-x_2\|_s^2\qquad\text{for all }x_1,x_2\in E.
--   $$
--
--   For example, the $\ell_p$-norm with $p\in[2,\infty)$ works with $L=p-1$.
--
--   **Formalization Note** $\langle\nabla g(x_1),v\rangle$ is the Fréchet derivative of $g$ at $x_1$ applied to $v$.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Appendix A, Notation, p.24

import Mathlib
import Definitions.Def_MarkovSA_IsNormFun

namespace MarkovSA

/-- The auxiliary norm `‖·‖_s` of the Notation paragraph (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, Appendix A, p.24): `s` has the norm
axioms and `g(x) = ½‖x‖_s²` is convex, differentiable and `L`-smooth with respect to `‖·‖_s`, `L > 0`:
`g(x₂) ≤ g(x₁) + ⟨∇g(x₁), x₂ − x₁⟩ + (L/2)‖x₁ − x₂‖_s²` for all `x₁, x₂`.

**Formalization Note.** `⟨∇g(x₁), v⟩` is the Fréchet derivative `fderiv ℝ g x₁ v`. -/
def IsSmoothNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (s : E → ℝ) (L : ℝ) : Prop :=
  IsNormFun s ∧ 0 < L ∧ ConvexOn ℝ Set.univ (fun x => (1 / 2 : ℝ) * s x ^ 2) ∧
    Differentiable ℝ (fun x => (1 / 2 : ℝ) * s x ^ 2) ∧
    ∀ x₁ x₂, (1 / 2 : ℝ) * s x₂ ^ 2 ≤
      (1 / 2 : ℝ) * s x₁ ^ 2 + fderiv ℝ (fun x => (1 / 2 : ℝ) * s x ^ 2) x₁ (x₂ - x₁) + L / 2 * s (x₁ - x₂) ^ 2

end MarkovSA


