-- Prove2me | Definitions.Def_RBMSensitivity_Data_localTime
-- name    : RBMSensitivity_Data_localTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:35.617994+00:00
-- url     : https://prove2.me/theorems/13024a03-9761-42e3-b149-74d735303392
-- title:
--   The local time process $L^\alpha$
-- statement:
--   Under Assumption 2.2, given an RBM $Z^\alpha$ with constraining process $Y^\alpha$, the **local time process** is
--   $$L^\alpha(t):=(R(\alpha))^{-1}Y^\alpha(t),\qquad t\ge 0.$$
--   Its $i$th component is the local time of $Z^\alpha$ on the face $F_i$ on $[0,t]$.
--
--   **Formalization Note** $Y^\alpha$ is determined by $Z^\alpha$ through (2.3), so the formal definition writes $Y^\alpha(t)=Z^\alpha(t)-Z^\alpha(0)-b(\alpha)t-\sigma(\alpha)W(t)$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, (2.3), (2.5), p.5–6

import Mathlib
import Definitions.Def_RBMSensitivity_Data_sigma
import Definitions.Def_RBMSensitivity_Data_R
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The local time process `L^α(t) := (R(α))⁻¹ Y^α(t)` of (2.5): arXiv:1907.00472v2, p.6.

**Formalization Note.** `Y^α` is determined by `Z^α` through (2.3), so `Y^α(t)` is written out as
`Z(t) - Z(0) - b(α)t - σ(α)W(t)`. Lean's matrix inverse is `0` at a singular matrix, so this is
meaningful only under Assumption 2.2, which makes `R(α)` invertible, and which every use assumes. -/
noncomputable def Data.localTime {J : ℕ} {Ω : Type*} (D : Data J) (W : ℝ≥0 → Ω → E J) (α : ℝ)
    (Z : ℝ≥0 → Ω → E J) (t : ℝ≥0) (ω : Ω) : E J :=
  Matrix.toEuclideanLin (D.R α)⁻¹
    (Z t ω - Z 0 ω - (t : ℝ) • D.b α - Matrix.toEuclideanLin (D.sigma α) (W t ω))

end RBMSensitivity


