-- Prove2me | Definitions.Def_ABPOnline_cG
-- name    : ABPOnline_cG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:37.667684+00:00
-- url     : https://prove2.me/theorems/294d8c54-870d-401d-b4a9-1080b7f7f81c
-- title:
--   Constants $c_G=\sqrt{2/\pi}$, $c_\alpha=\sqrt{2/(\pi\alpha)}$ and the Euclidean norm on $\mathbb R^M$
-- statement:
--   Let $\xi\sim N(0,1)$. The paper sets
--   $$
--   c_G:=\mathbb E|\xi|=\sqrt{\frac{2}{\pi}},\qquad c_\alpha:=\frac{c_G}{\sqrt\alpha}=\sqrt{\frac{2}{\pi\alpha}}\qquad(\alpha>0).
--   $$
--   The constant $c_G/\sqrt N$ is the radius of the ball of conditional drifts that one signed Gaussian column $\varepsilon Z$, $Z\sim N(0,I_M/N)$, can produce, and $c_\alpha$ is the corresponding limiting $L^2$ budget per coordinate when $M/N\to\alpha$. The module also defines the Euclidean norm $\|x\|_2=(\sum_i x_i^2)^{1/2}$ of $x\in\mathbb R^M$.
--
--   **Formalization Note** The closed forms are the definitions; vectors in $\mathbb R^M$ are functions on $\{0,\dots,M-1\}$, whose default Lean norm is the sup norm, so the Euclidean norm is written out.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), (9), p.7 (PDF p.8)

import Mathlib

set_option autoImplicit false

namespace ABPOnline

/-- The constant `c_G := E|ξ| = √(2/π)` for `ξ ∼ N(0,1)` (Jo–Lee, arXiv:2609.02124, (9), printed p.7,
PDF p.8).

**Formalization Note** The closed form `√(2/π)` is taken as the definition; the identity
`E|ξ| = √(2/π)` is a fact, not part of the definition. -/
noncomputable def cG : ℝ := Real.sqrt (2 / Real.pi)

/-- The drift budget `c_α := c_G/√α = √(2/(πα))` at constraint density `α`
(arXiv:2609.02124, (9), p.7). -/
noncomputable def cAlpha (α : ℝ) : ℝ := Real.sqrt (2 / (Real.pi * α))

/-- The Euclidean norm `‖x‖₂ = (∑ᵢ xᵢ²)^{1/2}` of a vector `x ∈ ℝ^M`.

**Formalization Note** Vectors in `ℝ^M` are functions `Fin M → ℝ`; Mathlib's norm on that type is
the sup norm, so the Euclidean norm used throughout the paper is written out explicitly. -/
noncomputable def l2norm {M : ℕ} (x : Fin M → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

end ABPOnline


