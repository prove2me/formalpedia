-- Prove2me | Definitions.Def_BrownianEnergyRep_IsHeatKernel
-- name    : BrownianEnergyRep_IsHeatKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:27.772974+00:00
-- url     : https://prove2.me/theorems/0921e791-c9f2-4bf8-b79c-6a28cd21017b
-- title:
--   The fundamental solution $p_t$ of the left heat equation (2.1)
-- statement:
--   Let $dx$ be a Haar measure on $G$. A family $p_t$, $t>0$, is the fundamental solution $p_t=e^{t\Delta/2}\delta_e$ of the left heat equation if
--   $$
--   \frac{\partial p_t}{\partial t}=\frac12\Delta p_t\quad\text{with}\quad \lim_{t\to0}p_t=\delta_e .
--   $$
--   This heat kernel gives the finite dimensional distributions of Wiener measure on $G$.
--
--   **Formalization Note** The conditions are: $p$ is jointly smooth on $(0,\infty)\times G$; the equation holds pointwise; and $\int_G p_tf\,dx\to f(e)$ as $t\downarrow0$ for every continuous $f$. They determine $p_t$ for all $t>0$, by Theorem 2.1 of this mission. Only $t>0$ is constrained.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, §2.1, (2.1), p.2

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra_laplacian
import Definitions.Def_BrownianEnergyRep_IsSmoothOnGroup

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `p` is the fundamental solution `p_t = e^{tΔ/2}δ_e` of the left heat equation (2.1),
`∂p_t/∂t = ½Δp_t` with `lim_{t→0} p_t = δ_e`, relative to the Haar measure `m = dx`
(arXiv:1511.07378v1, §2.1, (2.1), p.2).

**Formalization Note** Only `t > 0` matters: `p` is jointly smooth on `(0,∞) × G`, satisfies the
equation pointwise, and `∫ p_t f dm → f(e)` as `t ↓ 0` for continuous `f`. These conditions
determine `p_t` for every `t > 0` (`theorem_2_1`). Rescaling `m` rescales `p` inversely. -/
structure IsHeatKernel {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (m : Measure ↥G) (p : ℝ → ↥G → ℝ) : Prop where
  smooth : ∃ P : ℝ × (Fin n → Fin n → ℝ) → ℝ, ContDiffOn ℝ ∞ P (Ioi 0 ×ˢ univ) ∧
    ∀ t > 0, ∀ x, p t x = P (t, entries x)
  heat_equation : ∀ t > 0, ∀ x, deriv (fun s => p s x) t = (1 / 2) * L.laplacian (p t) x
  initial : ∀ f : ↥G → ℝ, Continuous f →
    Tendsto (fun t => ∫ x, p t x * f x ∂m) (𝓝[>] 0) (𝓝 (f 1))

end BrownianEnergyRep


