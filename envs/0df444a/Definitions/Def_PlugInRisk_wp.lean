-- Prove2me | Definitions.Def_PlugInRisk_wp
-- name    : PlugInRisk_wp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:41.73727+00:00
-- url     : https://prove2.me/theorems/28b2053f-9ac6-4b0a-a003-eb6ca96d382c
-- title:
--   Growth function $w_p$
-- statement:
--   For a risk measure $\rho$ on $L^p$ and $x\ge0$,
--
--   $$
--   w_p(x):=\sup\{\rho(X):\ \|X\|_{L^p}\le x\}\in[0,\infty].
--   $$
--
--   It is convex, nonnegative and grows at least linearly; for $p=\infty$ and for coherent $\rho$ it is linear. The integrability of $w_p(tJ^p)$ is the moment condition of Theorem 4.1 for unbounded data.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$; it is nonnegative because $\rho(0)=0$.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, §4, p.17

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Growth function** `w_p` (Bartl & Tangpi, arXiv:2003.10479v2, §4, p.17): "for every
parameter p ∈ [1, ∞] and x ≥ 0 set w_p(x) := sup{ρ(X) : ‖X‖_{Lᵖ} ≤ x}."

**Formalization Note** The supremum is taken in `[0, ∞]` (of `ENNReal.ofReal (ρ X)`), so it may
be `∞`. For a risk measure the set contains `ρ(0) = 0`, so the supremum is `≥ 0` and this equals
the paper's real-or-infinite supremum. Only `x ≥ 0` is used. -/
noncomputable def wp (p : ℝ≥0∞) (ρ : (unitInterval → ℝ) → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (X : unitInterval → ℝ) (_ : MemLp X p volume) (_ : eLpNorm X p volume ≤ ENNReal.ofReal x),
    ENNReal.ofReal (ρ X)

end PlugInRisk


