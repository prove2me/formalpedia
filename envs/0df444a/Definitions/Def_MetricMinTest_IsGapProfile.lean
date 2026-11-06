-- Prove2me | Definitions.Def_MetricMinTest_IsGapProfile
-- name    : MetricMinTest_IsGapProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:55.865453+00:00
-- url     : https://prove2.me/theorems/a56e2428-3936-40bd-8048-9315a879218d
-- title:
--   Gap profile $\gamma=g_0\ge\dots\ge g_m\ge0$
-- statement:
--   A **gap profile** is a sequence $\gamma=g_0\ge g_1\ge\dots\ge g_m\ge0$. It defines the hierarchical metric $d_g(x,y)=\gamma-g_{\mathrm{lev}(x,y)}$; a sample at hierarchical distance $t$ retains the gap $g_t$.
--
--   **Formalization Note** A function $\mathbb N\to\mathbb R$ of which only $g_0,\dots,g_m$ matter.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §4.1, p.8

import Mathlib

namespace MetricMinTest

/-- **Gap profile.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027
submission (manuscript sha256 dcece193…ad32bb), §4.1, p.8: "A gap profile
γ = g₀ ≥ g₁ ≥ ⋯ ≥ g_m ≥ 0".

**Formalization Note.** `g : ℕ → ℝ`; only `g 0, …, g m` matter. -/
def IsGapProfile (m : ℕ) (γ : ℝ) (g : ℕ → ℝ) : Prop :=
  g 0 = γ ∧ (∀ t < m, g (t + 1) ≤ g t) ∧ 0 ≤ g m

end MetricMinTest


