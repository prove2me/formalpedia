-- Prove2me | Definitions.Def_TeschlQM_Herglotz_lowerDeriv
-- name    : TeschlQM_Herglotz_lowerDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:33:57.42385+00:00
-- url     : https://prove2.me/theorems/c309cacc-ddd3-4b0d-8a1a-eaa49bc9865f
-- title:
--   Lower derivative of a Borel measure with respect to Lebesgue measure (A.45)
-- statement:
--   Let $\mu$ be a Borel measure on $\mathbb{R}$, write $B_\varepsilon(x) = (x - \varepsilon, x + \varepsilon)$ and let $|A|$ denote the Lebesgue measure of $A$. The **lower derivative** of $\mu$ at $x$ is
--   $$(\underline{D}\mu)(x) = \liminf_{\varepsilon \downarrow 0} \frac{\mu(B_\varepsilon(x))}{|B_\varepsilon(x)|} \in [0, \infty].$$
--
--   **Formalization Note.** The quotient is taken in `ℝ≥0∞` and the `liminf` is along `𝓝[>] 0`; for $\varepsilon > 0$ the denominator is $2\varepsilon \in (0,\infty)$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 283, Section A.8, Eq. (A.45)

import Mathlib

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TeschlQM.Herglotz

/-- Teschl, p. 283, (A.45): the **lower derivative** of a Borel measure `μ` on `ℝ`,
`(D̲μ)(x) = liminf_{ε↓0} μ(B_ε(x)) / |B_ε(x)|`, with `B_ε(x) = (x − ε, x + ε)` and `|·|` Lebesgue
measure. Valued in `[0, ∞]`. -/
noncomputable def lowerDeriv (μ : Measure ℝ) (x : ℝ) : ℝ≥0∞ :=
  liminf (fun ε : ℝ => μ (Metric.ball x ε) / volume (Metric.ball x ε)) (𝓝[>] (0 : ℝ))

end TeschlQM.Herglotz


