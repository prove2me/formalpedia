-- Prove2me | Definitions.Def_PhiSobBayes_Poincare
-- name    : PhiSobBayes_Poincare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:06:36.353895+00:00
-- url     : https://prove2.me/theorems/c09f0724-4359-41cf-bd65-587bb15a370c
-- title:
--   Poincaré inequality with constant $C$
-- statement:
--   A probability measure $\mu$ on $\mathbb R^n$ **satisfies the Poincaré inequality with constant $C$** if
--   $$\mathrm{Var}_\mu(f)\le C\,\mathbb E_\mu\|\nabla f\|_2^2\qquad\text{for every } f\in\mathcal A^{\mathbb R}_0.\tag{2}$$
--   The Poincaré constant $C_{\mathrm P}(\mu)$ is the least $C\ge0$ for which this holds.
--
--   It appears in the conclusion of the Bakry–Émery milestone, $C_{\mathrm P}(\mu)\le 1/\rho$ for $\rho$-strongly log-concave $\mu$.
--
--   **Formalization Note** $\mathrm{Var}_\mu$ is Mathlib's `variance`. The statement "$C_{\mathrm P}(\mu)\le c$" is expressed as "`Poincare μ c`": the set of valid constants is closed and upward closed, so the least constant is at most $c$ exactly when $c$ is valid.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 2, p.3 (PDF 3), display (2)

import Mathlib
import Definitions.Def_PhiSobBayes_testClass

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- `μ` satisfies the **Poincaré inequality with constant `C`**:
`Var_μ(f) ≤ C 𝔼_μ ‖∇f‖₂²` for every `f ∈ A^ℝ_0`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 2, p.3 (PDF 3), display (2).

**Formalization Note** `Var_μ` is Mathlib's `ProbabilityTheory.variance` (finite for the bounded test
functions). The paper's Poincaré constant `C_P(μ)` is the least valid `C ≥ 0`; "`C_P(μ) ≤ c`" is
"`Poincare μ c`", because the valid constants form a closed up-set. -/
def Poincare {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (C : ℝ) : Prop :=
  ∀ f ∈ testClass n Set.univ, variance f μ ≤ C * ∫ x, ‖gradient f x‖ ^ 2 ∂μ

end PhiSobBayes


