-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_HomogeneousOfDegree
-- name    : BauerleRiederMDP_TransactionCosts_HomogeneousOfDegree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:23.079508+00:00
-- url     : https://prove2.me/theorems/f4e3ecf3-cfae-44d0-a7c2-7147e0418a5d
-- title:
--   Homogeneity of degree $\gamma$
-- statement:
--   A function $v:E\to[-\infty,\infty)$ is homogeneous of degree $\gamma$ if
--   $$v(\lambda x_0,\lambda x_1)=\lambda^\gamma v(x_0,x_1)\qquad\text{for all }\lambda>0,\ (x_0,x_1)\in E.$$
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, p.107 (PDF 121)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace

namespace BauerleRiederMDP.TransactionCosts

/-- A function `v : E → [−∞, ∞)` is *homogeneous of degree `γ`* (Bäuerle & Rieder 2011, §4.5,
p.107, PDF 121): `v(λx₀, λx₁) = λ^γ v(x₀, x₁)` for all `λ > 0` and `(x₀, x₁) ∈ E`. -/
def HomogeneousOfDegree (γ : ℝ) (v : ℝ × ℝ → EReal) : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ x ∈ stateSpace,
    v (lam * x.1, lam * x.2) = ((lam ^ γ : ℝ) : EReal) * v x

end BauerleRiederMDP.TransactionCosts


