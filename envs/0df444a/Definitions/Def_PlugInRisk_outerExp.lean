-- Prove2me | Definitions.Def_PlugInRisk_outerExp
-- name    : PlugInRisk_outerExp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:40.325087+00:00
-- url     : https://prove2.me/theorems/863903b6-5a39-4ad2-9340-d3e3e78e21a4
-- title:
--   Outer expectation $E^*$
-- statement:
--   For a function $Z:\Omega\to[0,\infty]$ on a probability space $(\Omega,\mathcal F,P)$, not necessarily measurable, the **outer expectation** is
--
--   $$
--   E^*[Z]:=\inf\{E[Y]: Y\ge Z,\ Y:\Omega\to[0,\infty]\text{ measurable}\}.
--   $$
--
--   It agrees with $E[Z]$ for measurable $Z$. The paper uses $E^*$ and the outer probability $P^*$ because the plug-in estimator need not be measurable.
--
--   **Formalization Note** The outer probability of an arbitrary set is Mathlib's measure of that set, which is the outer measure; no separate definition is needed.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, p.4 (citing van der Vaart and Wellner [50])

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Outer expectation** `E*` (Bartl & Tangpi, arXiv:2003.10479v2, p.4: "E* and P* denote the
outer expectation and outer probability, respectively, see, e.g., [50]. They are used since
ρ^{μ_N} does not necessarily need to be measurable").

For `Z : Ω → [0, ∞]`, `E*[Z]` is the infimum of `E[Y]` over measurable majorants `Y ≥ Z`
(van der Vaart and Wellner, §1.2).

**Formalization Note** Mathlib's `∫⁻` of a non-measurable function is the lower integral, so it
is not used for `E*`. For measurable `Z`, `outerExp P Z = ∫⁻ Z ∂P`. The outer probability `P*`
of an arbitrary set `s` is Mathlib's `P s`, which is the outer measure. -/
noncomputable def outerExp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ≥0∞) :
    ℝ≥0∞ :=
  ⨅ (Y : Ω → ℝ≥0∞) (_ : Measurable Y) (_ : Z ≤ Y), ∫⁻ ω, Y ω ∂P

end PlugInRisk


