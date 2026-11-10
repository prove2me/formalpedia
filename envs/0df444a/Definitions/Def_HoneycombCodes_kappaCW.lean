-- Prove2me | Definitions.Def_HoneycombCodes_kappaCW
-- name    : HoneycombCodes_kappaCW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:28:41.238189+00:00
-- url     : https://prove2.me/theorems/3eb3557d-af0b-44d8-a27e-68e200132d0e
-- title:
--   Constant-weight exponent $\kappa_{CW}(\delta)$, $\Lambda_{\alpha,\beta,\gamma}$, $\Phi_{CW}$, $E_{CW}$ and $\kappa_{bin}=\min\{\kappa_H,\kappa_{CW}\}$
-- statement:
--   The constant-weight branch of OpenAI's moving-projection bound has parameters satisfying
--
--   $$
--   \tfrac{\delta}{2}<\alpha<\tfrac12,\quad 0\le\beta<\tfrac{\alpha}{2},\quad 0\le\gamma<\tfrac{1-\alpha}{2},\quad
--   \beta+\gamma<u<\min\{\alpha,\ \alpha-\beta+\gamma,\ 1-\alpha+\beta-\gamma\}. \tag{76–77}
--   $$
--
--   With $z=1-2u$, $m=1-2\alpha$, $\zeta=1-2\beta-2\gamma$, $\xi=1-2\alpha+2\beta-2\gamma$ define
--
--   $$
--   \Lambda_{\alpha,\beta,\gamma}(u)=\frac{(\zeta\xi-mz^2)^2}{z^2(1-m^2)(1-z^2)}+\frac{(z^2-\xi^2)(\zeta^2-z^2)}{z^2(1-m^2)\sqrt{1-z^2}},
--   $$
--
--   $$
--   \Phi_{CW}(\alpha,\beta,\gamma,w)=1-H_2(\alpha)+H_2(w)-\alpha H_2(\beta/\alpha)-(1-\alpha)H_2\bigl(\gamma/(1-\alpha)\bigr),\qquad
--   E_{CW}=2\alpha(1-\alpha)\bigl(1-\Lambda_{\alpha,\beta,\gamma}(w)\bigr).
--   $$
--
--   The **constant-weight exponent** is the infimum of $\Phi_{CW}(\alpha,\beta,\gamma,u)$ over the points satisfying (76)–(77) and the strict spectral condition
--
--   $$
--   \Lambda_{\alpha,\beta,\gamma}(u)>1-\frac{\delta}{2\alpha(1-\alpha)}, \tag{80}
--   $$
--
--   and $\kappa_{bin}(\delta)=\min\{\kappa_H(\delta),\kappa_{CW}(\delta)\}$ is the previous combined moving-projection exponent.
--
--   **Formalization Note** A real `sInf` over the strictly feasible points. The ranges, $\Lambda$, the threshold and the objective are those of the published `MetricCodes.Johnson.variationalRate` (`AsymptoticParameters`, `spectralLimit`, `asymptoticThreshold`, `shellRate`), mirrored here because that module is not in this workspace.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §6.5, eqs. (76)–(80), p.34 (PDF 36); Φ_CW and E_CW: eq. (131), p.63 (PDF 65); κ_bin: §1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaH

set_option autoImplicit false

namespace HoneycombCodes

/-- The constant-weight spectral limit (79),
`Λ_{α,β,γ}(u) = (ζξ − m z²)²/(z²(1 − m²)(1 − z²)) + (z² − ξ²)(ζ² − z²)/(z²(1 − m²)√(1 − z²))`
with `z = 1 − 2u`, `m = 1 − 2α`, `ζ = 1 − 2β − 2γ`, `ξ = 1 − 2α + 2β − 2γ` (78),
Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2
(sha256 f4b07e31…cd51), §6.5, p.34 (PDF 36). Mirrors `MetricCodes.Johnson.spectralLimit`. -/
noncomputable def LambdaCW (α β γ u : ℝ) : ℝ :=
  let z := 1 - 2 * u
  let m := 1 - 2 * α
  let ζ := 1 - 2 * β - 2 * γ
  let ξ := 1 - 2 * α + 2 * β - 2 * γ
  (ζ * ξ - m * z ^ 2) ^ 2 / (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
    (z ^ 2 - ξ ^ 2) * (ζ ^ 2 - z ^ 2) / (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2))

/-- The constant-weight range conditions (76)–(77), arXiv:2608.20287v2, p.34 (PDF 36):
`δ/2 < α < 1/2`, `0 ≤ β < α/2`, `0 ≤ γ < (1 − α)/2`,
`β + γ < u < min{α, α − β + γ, 1 − α + β − γ}`. -/
def CWRange (δ α β γ u : ℝ) : Prop :=
  δ / 2 < α ∧ α < 1 / 2 ∧ 0 ≤ β ∧ β < α / 2 ∧ 0 ≤ γ ∧ γ < (1 - α) / 2 ∧
    β + γ < u ∧ u < α ∧ u < α - β + γ ∧ u < 1 - α + β - γ

/-- The constant-weight objective (131),
`Φ_CW(α, β, γ, w) = 1 − H₂(α) + H₂(w) − α H₂(β/α) − (1 − α) H₂(γ/(1 − α))`,
arXiv:2608.20287v2, App. D.4, p.63 (PDF 65); the same expression is the objective of `κ_CW`
in §6.5, p.34. Mirrors `MetricCodes.Johnson.shellRate`. -/
noncomputable def PhiCW (α β γ w : ℝ) : ℝ :=
  1 - H2 α + H2 w - α * H2 (β / α) - (1 - α) * H2 (γ / (1 - α))

/-- The constant-weight effective error `E_CW(α, β, γ, w) = 2α(1 − α)(1 − Λ_{α,β,γ}(w))`,
arXiv:2608.20287v2, App. D.4, p.63 (PDF 65). -/
noncomputable def ECW (α β γ w : ℝ) : ℝ :=
  2 * α * (1 - α) * (1 - LambdaCW α β γ w)

/-- The **constant-weight exponent** of [OAI26],
`κ_CW(δ) = inf over (76)–(77) and Λ_{α,β,γ}(u) > 1 − δ/(2α(1 − α)) (80) of Φ_CW(α, β, γ, u)`,
arXiv:2608.20287v2, §6.5, p.34 (PDF 36).

**Formalization Note.** A real `sInf` of the objective values over the strictly feasible points
(strict constraint (80), as printed). Mirrors the published `MetricCodes.Johnson.variationalRate`
(the same twelve range conditions and the same strict spectral condition). -/
noncomputable def kappaCW (δ : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ α β γ u : ℝ, CWRange δ α β γ u ∧
    1 - δ / (2 * α * (1 - α)) < LambdaCW α β γ u ∧ r = PhiCW α β γ u}

/-- The previous combined moving-projection exponent `κ_bin = min{κ_H, κ_CW}`,
arXiv:2608.20287v2, §1, p.1 (PDF 3) and §6.5, p.34. Mirrors
`MetricCodes.Johnson.combinedVariationalRate`. -/
noncomputable def kappaBin (δ : ℝ) : ℝ :=
  min (kappaH δ) (kappaCW δ)

end HoneycombCodes


