-- Prove2me | Definitions.Def_StrategicObfuscation_equilibriumEffort
-- name    : StrategicObfuscation_equilibriumEffort
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:03.977019+00:00
-- url     : https://prove2.me/theorems/3b0b23cf-d09e-4c01-8504-53bc4e882803
-- title:
--   Equilibrium effort $e^*(\sigma)$ of a family of funding probabilities
-- statement:
--   Given a family $\alpha^*(\sigma)$ of funding probabilities, the equilibrium effort at $\sigma$ is $e^*(\sigma)=E(\alpha^*(\sigma),\sigma)$. This is the curve drawn in Figure 3a of the paper.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), Definition 1, clause 1, p.10, and Figure 3a, p.13

import Mathlib

namespace StrategicObfuscation

/-- **The equilibrium effort `e*(σ) = e(α*(σ), σ)` of a family of funding probabilities.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), Definition 1, clause 1, p.10 (PDF p.10), and Figure 3a,
p.13 (PDF p.13), where `e*` is drawn as a function of `σ`.

**Formalization Note** `αS` gives the funding probability at each `σ`. -/
def equilibriumEffort (E : ℝ → ℝ → ℝ) (αS : ℝ → ℝ) (σ : ℝ) : ℝ :=
  E (αS σ) σ

end StrategicObfuscation


