-- Prove2me | Definitions.Def_TeschlQM_Herglotz_upperDeriv
-- name    : TeschlQM_Herglotz_upperDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:33:36.122302+00:00
-- url     : https://prove2.me/theorems/9574bbf6-9126-4654-8a01-172d8f79270b
-- title:
--   Upper derivative of a Borel measure with respect to Lebesgue measure (A.45)
-- statement:
--   Let $\mu$ be a Borel measure on $\mathbb{R}$, write $B_\varepsilon(x) = (x - \varepsilon, x + \varepsilon)$ and let $|A|$ denote the Lebesgue measure of $A$. The **upper derivative** of $\mu$ at $x$ is
--   $$(\overline{D}\mu)(x) = \limsup_{\varepsilon \downarrow 0} \frac{\mu(B_\varepsilon(x))}{|B_\varepsilon(x)|} \in [0, \infty].$$
--
--   **Formalization Note.** The quotient is taken in `ℝ≥0∞` and the `limsup` is along `𝓝[>] 0`, the right neighbourhoods of $0$; for $\varepsilon > 0$ the denominator is $2\varepsilon \in (0,\infty)$. The value $\infty$ is allowed.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 283, Section A.8, Eq. (A.45)

import Mathlib

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TeschlQM.Herglotz

/-- Teschl, p. 283, (A.45): the **upper derivative** of a Borel measure `μ` on `ℝ`,
`(D̄μ)(x) = limsup_{ε↓0} μ(B_ε(x)) / |B_ε(x)|`, with `B_ε(x) = (x − ε, x + ε)` and `|·|` Lebesgue
measure. Valued in `[0, ∞]`. -/
noncomputable def upperDeriv (μ : Measure ℝ) (x : ℝ) : ℝ≥0∞ :=
  limsup (fun ε : ℝ => μ (Metric.ball x ε) / volume (Metric.ball x ε)) (𝓝[>] (0 : ℝ))

end TeschlQM.Herglotz


