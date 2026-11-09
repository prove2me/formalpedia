-- Prove2me | Definitions.Def_PhiSobBayes_PhiSobolev
-- name    : PhiSobBayes_PhiSobolev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:06:48.865136+00:00
-- url     : https://prove2.me/theorems/8ff64e19-6f8c-4a72-8968-df4b43f1482a
-- title:
--   $\Phi$-Sobolev inequality with constant $C$
-- statement:
--   Let $\mu$ be a measure on $\mathbb R^n$, $J$ an open interval and $\Phi:J\to\mathbb R$. The measure $\mu$ **satisfies the $\Phi$-Sobolev inequality with constant $C$** if
--   $$\mathrm{Ent}^\Phi_\mu(f)\le\frac C2\,\mathbb E_\mu\big[\Phi''(f)\,\|\nabla f\|_2^2\big]\qquad\text{for every } f\in\mathcal A^J_0.\tag{1}$$
--
--   With $\Phi(z)=(z-1)^2$ on $\mathbb R$ this is the Poincaré inequality, and with $\Phi(z)=z\log z$ on $(0,\infty)$ it becomes the log-Sobolev inequality after substituting $f=g^2$. It is condition (i) of the goal theorem.
--
--   **Formalization Note** Only $\mathcal A^J_0$ is tested. $\Phi''$ is `deriv (deriv Φ)` and $\nabla f$ is the Euclidean `gradient`.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 1, p.3 (PDF 3), display (1)

import Mathlib
import Definitions.Def_PhiSobBayes_testClass
import Definitions.Def_PhiSobBayes_phiEnt

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- `μ` satisfies the **Φ-Sobolev inequality with constant `C`**:
`Ent^Φ_μ(f) ≤ (C/2) 𝔼_μ[Φ″(f) ‖∇f‖₂²]` for every `f ∈ A^J_0`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 1, p.3 (PDF 3), display (1).

**Formalization Note** Only the test class `A^J_0` is tested, exactly as in Definition 1. `Φ″` is
`deriv (deriv Φ)` and `∇f` is `gradient f` for the Euclidean inner product. -/
def PhiSobolev {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (J : Set ℝ) (Φ : ℝ → ℝ)
    (C : ℝ) : Prop :=
  ∀ f ∈ testClass n J,
    phiEnt μ Φ f ≤ C / 2 * ∫ x, deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2 ∂μ

end PhiSobBayes


