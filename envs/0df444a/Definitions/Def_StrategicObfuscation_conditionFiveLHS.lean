-- Prove2me | Definitions.Def_StrategicObfuscation_conditionFiveLHS
-- name    : StrategicObfuscation_conditionFiveLHS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:21.069355+00:00
-- url     : https://prove2.me/theorems/c496d92f-e91e-46e8-b021-ee6420641012
-- title:
--   The left-hand side of inequality (5)
-- statement:
--   For an effort curve $e^*$, this is the total effect of resources on detection at maximal obfuscation,
--
--   $$\frac{\partial\pi(\sigma,e^*)}{\partial\sigma}+\frac{\partial\pi(\sigma,e^*)}{\partial e}\,\frac{\partial e^*}{\partial\sigma}.$$
--
--   **Formalization Note** The partial in $\sigma$ is at the frozen effort $e^*(\sigma)$. The partial in $e$ is a derivative within $[0,\infty)$, so it is the right derivative at $e^*=0$. `deriv` returns $0$ at a non-differentiable point, so statements using this term assume differentiability at the point.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), Proposition 2, eq. (5), p.13

import Mathlib

open Set

namespace StrategicObfuscation

/-- **The left-hand side of inequality (5).**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), Proposition 2, eq. (5), p.13 (PDF p.13):
`∂π(σ, e*)/∂σ + (∂π(σ, e*)/∂e) (∂e*/∂σ)`, evaluated at `σ` with `e* = eS σ`.

**Formalization Note** The partial in `σ` is taken at the frozen effort `eS σ`. The partial in `e`
is a derivative within `[0, ∞)`, so it is the right derivative at `e* = 0`, where `π` carries no
meaning to the left. `deriv` and `derivWithin` return `0` at a non-differentiable point, so the
statements using this term assume differentiability at the point. -/
noncomputable def conditionFiveLHS (π : ℝ → ℝ → ℝ) (eS : ℝ → ℝ) (σ : ℝ) : ℝ :=
  deriv (fun s => π s (eS σ)) σ + derivWithin (π σ) (Ici 0) (eS σ) * deriv eS σ

end StrategicObfuscation


