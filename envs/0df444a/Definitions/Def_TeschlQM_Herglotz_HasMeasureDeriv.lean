-- Prove2me | Definitions.Def_TeschlQM_Herglotz_HasMeasureDeriv
-- name    : TeschlQM_Herglotz_HasMeasureDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:34:20.819345+00:00
-- url     : https://prove2.me/theorems/350759e7-25cd-42db-a7be-f693a9248992
-- title:
--   The derivative (Dμ)(x) of a Borel measure exists and equals d (A.44)
-- statement:
--   Let $\mu$ be a Borel measure on $\mathbb{R}$ and $B_\varepsilon(x) = (x - \varepsilon, x + \varepsilon)$. The **derivative** of $\mu$ at $x$ is
--   $$(D\mu)(x) = \lim_{\varepsilon \downarrow 0} \frac{\mu(B_\varepsilon(x))}{|B_\varepsilon(x)|},$$
--   provided the limit exists. The predicate $\mathrm{HasMeasureDeriv}(\mu, x, d)$ says that this limit exists and equals $d \in [0, \infty]$; the value $d = \infty$ is allowed, as in the book's use of the set $\{x \mid (D\mu)(x) = \infty\}$.
--
--   **Formalization Note.** Convergence is in the order topology of `ℝ≥0∞`, along `𝓝[>] 0`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, pp. 282–283, Section A.8, Eq. (A.44)

import Mathlib

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TeschlQM.Herglotz

/-- Teschl, pp. 282–283, (A.44): `HasMeasureDeriv μ x d` says that the **derivative**
`(Dμ)(x) = lim_{ε↓0} μ(B_ε(x)) / |B_ε(x)|` of the Borel measure `μ` exists at `x` and equals
`d ∈ [0, ∞]` (the value `∞` is allowed, as in Theorem A.38). Here `B_ε(x) = (x − ε, x + ε)` and
`|·|` is Lebesgue measure. -/
def HasMeasureDeriv (μ : Measure ℝ) (x : ℝ) (d : ℝ≥0∞) : Prop :=
  Tendsto (fun ε : ℝ => μ (Metric.ball x ε) / volume (Metric.ball x ε)) (𝓝[>] (0 : ℝ)) (𝓝 d)

end TeschlQM.Herglotz


