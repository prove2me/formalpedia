-- Prove2me | Definitions.Def_PlugInRisk_IsQRegular
-- name    : PlugInRisk_IsQRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:28.116771+00:00
-- url     : https://prove2.me/theorems/85de0f14-5c18-4b7d-b6fc-ff250a906ff0
-- title:
--   $q$-regular risk measure, Definition 2.1
-- statement:
--   For $q\in(1,\infty)$, a risk measure $\rho$ is **$q$-regular** if
--
--   $$
--   \sup_{n\in\mathbb N}\rho(X\wedge n)<\infty
--   $$
--
--   for every random variable $X$ on the standard probability space whose law is Pareto with shape parameter $q$ (and any scale $x>0$).
--
--   This continuity condition is stronger than the Fatou and Lebesgue properties; it is what yields the convergence rate $N^{-1/(2q)}$ of the plug-in estimator.
--
--   **Formalization Note** $X$ ranges over measurable functions on $[0,1]$ with Pareto law; the truncations $X\wedge n$ are bounded. Since $\rho$ is real valued, the supremum being finite is boundedness from above.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Definition 2.1, p.7

import Mathlib
import Definitions.Def_PlugInRisk_IsPareto

open MeasureTheory

namespace PlugInRisk

/-- **q-regularity** (Bartl & Tangpi, arXiv:2003.10479v2, Definition 2.1, p.7): for
`q ∈ (1, ∞)` a convex risk measure is `q`-regular if `sup_{n∈ℕ} ρ(X ∧ n) < ∞` for all random
variables `X` following a Pareto distribution with shape parameter `q`.

**Formalization Note** Random variables live on the standard probability space `[0,1]` with
Lebesgue measure; `X` ranges over measurable functions whose law is Pareto with some scale
`x > 0` and shape `q`. Each truncation `X ∧ n` is bounded, so it lies in every `Lᵖ`. Since `ρ` is
real-valued, `sup_n ρ(X ∧ n) < ∞` is `BddAbove` of the range. The restriction `q ∈ (1, ∞)` is
imposed by the theorems that use the notion. -/
def IsQRegular (q : ℝ) (ρ : (unitInterval → ℝ) → ℝ) : Prop :=
  ∀ (X : unitInterval → ℝ) (x : ℝ), 0 < x → Measurable X → IsPareto (volume.map X) x q →
    BddAbove (Set.range fun n : ℕ => ρ (fun ω => min (X ω) (n : ℝ)))

end PlugInRisk


