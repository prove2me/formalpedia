-- Prove2me | Definitions.Def_FastRatesSVM_GeomNoise_GeometricNoise
-- name    : FastRatesSVM_GeomNoise_GeometricNoise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:29.549421+00:00
-- url     : https://prove2.me/theorems/d8f7a0ee-0564-4281-803c-708b359354ea
-- title:
--   Definition 2.3 — geometric noise exponent $\alpha$: $\int_X |2\eta-1| e^{-\tau_x^2/t}\,dP_X \le C t^{\alpha d/2}$
-- statement:
--   Let $X \subset \mathbb R^d$ be compact and $P$ a probability measure on $X \times \{-1, 1\}$ with marginal $P_X$, regression function $\eta$ and distance to the decision boundary $\tau_x$ (equation (7)). The distribution $P$ has **geometric noise exponent** $\alpha > 0$ if there is a constant $C > 0$ such that
--
--   $$\int_X |2\eta(x) - 1| \exp\Big(-\frac{\tau_x^2}{t}\Big)\, P_X(dx) \le C\, t^{\alpha d/2}, \qquad t > 0.$$
--
--   It has **geometric noise exponent $\infty$** if it has geometric noise exponent $\alpha$ for every $\alpha > 0$.
--
--   The condition measures how much of the measure $|2\eta - 1|\,dP_X$ sits near the decision boundary: the less concentrated it is there, the larger the exponent. It requires neither smoothness of $\eta$ nor absolute continuity of $P_X$, and it is the hypothesis under which the paper bounds the approximation error of Gaussian RBF kernels.
--
--   **Formalization Note** The integral of the nonnegative integrand is the Lebesgue integral with values in $[0, \infty]$ (`lintegral`), so no integrability side condition can make the bound hold vacuously. The requirement $\alpha > 0$ is part of the definition, as on the page. Compactness of $X$ belongs to the theorems that use the definition, not to the definition. $d$ is the dimension of the ambient space `EuclideanSpace ℝ (Fin d)`.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 7, Definition 2.3, equation (8)

import Mathlib
import Definitions.Def_FastRatesSVM_GeomNoise_Tau

open MeasureTheory

namespace FastRatesSVM.GeomNoise

/-- **Geometric noise exponent** `α > 0`, Definition 2.3, p. 7 (Steinwart–Scovel,
arXiv:0708.1838v1): `α > 0` and there is `C > 0` with
`∫_X |2η(x) − 1| exp(−τ_x² / t) P_X(dx) ≤ C t^{αd/2}` for all `t > 0` (equation (8)).
The integral of the nonnegative integrand is the lower Lebesgue integral in `[0, ∞]`. -/
def HasGeometricNoiseExponent {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (η : EuclideanSpace ℝ (Fin d) → ℝ) (α : ℝ) :
    Prop :=
  0 < α ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
    (∫⁻ x in X, ENNReal.ofReal (|2 * η x - 1| * Real.exp (-(tau X η x) ^ 2 / t)) ∂μ) ≤
      ENNReal.ofReal (C * t ^ (α * (d : ℝ) / 2))

/-- **Geometric noise exponent `∞`**, Definition 2.3, p. 7: geometric noise exponent `α` for
every `α > 0`. -/
def HasGeometricNoiseExponentTop {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (η : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → HasGeometricNoiseExponent X μ η α

end FastRatesSVM.GeomNoise


