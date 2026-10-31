-- Prove2me | Definitions.Def_SweepingDesing_IsLocallyAC
-- name    : SweepingDesing_IsLocallyAC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:00.99131+00:00
-- url     : https://prove2.me/theorems/ab5c4678-eba7-411f-8c89-e91fbcb03f37
-- title:
--   §2.1 — absolute continuity of a curve on an interval
-- statement:
--   A curve $\gamma:I\to\mathbb R^n$ on an interval $I\subset\mathbb R$ is **absolutely continuous on $I$** if it is absolutely continuous on every compact interval $[c,d]\subseteq I$.
--
--   For a compact interval this is ordinary absolute continuity; for the half-open and open intervals that occur in the paper ($[t,t+\delta)$, $[a,b)$, $(a,b)$, and the pieces of a piecewise absolutely continuous curve) it is local absolute continuity.
--
--   **Formalization Note** Built on Mathlib's `AbsolutelyContinuousOnInterval`; values of $\gamma$ off $I$ play no role.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §2.1, Definition 2 and the paragraph on piecewise absolutely continuous curves, p.4

import Mathlib
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §2.1, p.4 (Definition 2 and the paragraph on piecewise absolutely continuous curves):
a curve `γ` is *absolutely continuous on the interval* `I`.

**Formalization Note** Read as: `γ` is absolutely continuous on every compact interval
`[c, d] ⊆ I` (Mathlib's `AbsolutelyContinuousOnInterval`). For a compact `I` this is absolute
continuity on `I`; for the half-open and open intervals of the paper (`[t, t + δ)`, `[a, b)`,
`(a, b)`, the pieces `J_i`) it is the usual `W^{1,1}_loc` reading. Values of `γ` off `I` play no
role. -/
def IsLocallyAC {n : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin n)) (I : Set ℝ) : Prop :=
  ∀ c d : ℝ, c ≤ d → Icc c d ⊆ I → AbsolutelyContinuousOnInterval γ c d

end SweepingDesing


