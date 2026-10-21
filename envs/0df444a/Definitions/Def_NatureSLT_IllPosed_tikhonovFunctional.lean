-- Prove2me | Definitions.Def_NatureSLT_IllPosed_tikhonovFunctional
-- name    : NatureSLT_IllPosed_tikhonovFunctional
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:14.327008+00:00
-- url     : https://prove2.me/theorems/001f1cc5-9e73-4d70-a324-a20d09ac9b75
-- title:
--   Tikhonov functional $W_T(g) = \rho^2_{E_2}(Ag, F) + \gamma\,\Omega(g)$
-- statement:
--   Let $E_1$ be a set, $(E_2, \rho_{E_2})$ a metric space, $A : E_1 \to E_2$ a map, $\Omega : E_1 \to [0,\infty]$ a functional, $\gamma$ a real parameter and $F \in E_2$ a right-hand side. **Tikhonov's functional** (Method T) is
--
--   $$W_T(g) = \rho^2_{E_2}(A g, F) + \gamma\, \Omega(g), \qquad g \in E_1,$$
--
--   with values in $[0, \infty]$.
--
--   Method T solves the equation $A f = F$ approximately by minimizing $W_T$; the first term measures how well $g$ fits the data, the second penalizes irregular $g$, and $\gamma$ trades one against the other. Theorems 7.1–7.5 use it with an approximate right-hand side $F_\delta$ or $F_\ell$ and, in §7.9.1, with an approximate operator $A_\ell$.
--
--   **Formalization Note** The functional is written in the metric form (7.19), $\rho^2_{E_2}(Af, F)$, which in a normed space is $\|Af - F\|^2_{E_2}$ as on p. 235. For $\gamma > 0$ its value is $\infty$ exactly off the domain $\{\Omega < \infty\}$ of $\Omega$. The parameter $\gamma$ is not restricted here; every theorem using it assumes $\gamma > 0$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 235, Section 7.5 (Method T), with Eq. (7.19), p. 238

import Mathlib

namespace NatureSLT.IllPosed

open scoped ENNReal

/-- Tikhonov's functional of Method T (Vapnik, *The Nature of Statistical Learning Theory*,
2nd ed., §7.5, p. 235, in the metric form (7.19) of p. 238):
`W_T(g) = ρ²_{E₂}(A g, F) + γ Ω(g)`, for an operator `A : E₁ → E₂` into a metric space, a
regularization functional `Ω : E₁ → [0, ∞]`, a parameter `γ` and a right-hand side `F ∈ E₂`.

The value is in `[0, ∞]`; it is `∞` exactly when `γ > 0` and `g` lies outside the domain
`{Ω < ∞}` of `Ω`. -/
noncomputable def tikhonovFunctional {E₁ E₂ : Type*} [MetricSpace E₂] (A : E₁ → E₂)
    (Ω : E₁ → ℝ≥0∞) (γ : ℝ) (F : E₂) (g : E₁) : ℝ≥0∞ :=
  ENNReal.ofReal (dist (A g) F ^ 2) + ENNReal.ofReal γ * Ω g

end NatureSLT.IllPosed


