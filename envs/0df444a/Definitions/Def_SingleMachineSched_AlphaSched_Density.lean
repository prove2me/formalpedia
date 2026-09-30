-- Prove2me | Definitions.Def_SingleMachineSched_AlphaSched_Density
-- name    : SingleMachineSched_AlphaSched_Density
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:11:02.722012+00:00
-- url     : https://prove2.me/theorems/d047560b-11bd-4691-b216-1ccfbfccb2aa
-- title:
--   The constants $c$, $\delta$ and the truncated exponential density $f$ of Theorem 3.5
-- statement:
--   For a real parameter $\gamma$ define
--
--   $$c = \frac{1 + \gamma}{1 + \gamma - e^{-\gamma}}, \qquad \delta = 1 - \frac{\gamma^2}{1 + \gamma},$$
--
--   and the truncated exponential function
--
--   $$f(\alpha) = \begin{cases} (c - 1)\, e^{\alpha} & \text{if } 0 < \alpha \le \delta, \\ 0 & \text{otherwise.} \end{cases}$$
--
--   The random $\alpha$ of Theorem 3.5 has law $f(\alpha)\,d\alpha$ on $\mathbb R$.
--
--   In the paper $\gamma \approx 0.4675$ is the root in $(0,1)$ of $1 - \gamma^2/(1+\gamma) = \gamma + \ln(1+\gamma)$. Then $c \approx 1.7451$, $\delta \approx 0.8511$, $\delta = \ln\frac{c}{c-1}$, and $f$ integrates to $1$.
--
--   **Formalization Note** The paper writes "$f(\alpha) = (c-1)e^\alpha$ if $\alpha \le \delta$, $0$ otherwise" for $\alpha$ on its domain $(0, 1]$; the condition $0 < \alpha$ is written out so that no mass sits on $(-\infty, 0]$. The measure is Lebesgue measure with density $\max(f, 0)$; $f \ge 0$ at the paper's $\gamma$. The constants are functions of $\gamma$; the equation for $\gamma$ is a hypothesis of the theorems.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 183, Theorem 3.5 (definitions of $c$, $\delta$, $f$)

import Mathlib

namespace SingleMachineSched.AlphaSched

open MeasureTheory

/-- The constant `c = (1 + γ) / (1 + γ - e^{-γ})` of Theorem 3.5 (p. 183). -/
noncomputable def cConst (γ : ℝ) : ℝ :=
  (1 + γ) / (1 + γ - Real.exp (-γ))

/-- The constant `δ = 1 - γ² / (1 + γ)` of Theorem 3.5 (p. 183). -/
noncomputable def deltaConst (γ : ℝ) : ℝ :=
  1 - γ ^ 2 / (1 + γ)

/-- The truncated exponential density `f` of Theorem 3.5 (p. 183) on its domain `(0, 1]`:
`f(α) = (c - 1) e^α` for `0 < α ≤ δ`, and `0` otherwise. -/
noncomputable def fDens (γ : ℝ) (a : ℝ) : ℝ :=
  if 0 < a ∧ a ≤ deltaConst γ then (cConst γ - 1) * Real.exp a else 0

/-- The law on `ℝ` with density `f` with respect to Lebesgue measure. -/
noncomputable def fMeasure (γ : ℝ) : Measure ℝ :=
  volume.withDensity (fun a => ENNReal.ofReal (fDens γ a))

end SingleMachineSched.AlphaSched


