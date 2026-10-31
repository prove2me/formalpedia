-- Prove2me | Definitions.Def_RBMSensitivity_Data_M0
-- name    : RBMSensitivity_Data_M0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:35:23.200007+00:00
-- url     : https://prove2.me/theorems/0522c70e-1147-4085-aa73-447386adfd8d
-- title:
--   The function $M_0$
-- statement:
--   Given a compact subset $U_0$ of $U$,
--   $$M_0(x):=\sup_{\alpha\in U_0}M^\alpha(x),\qquad x\in G.$$
--
--   It makes the Lyapunov analysis uniform in $\alpha\in U_0$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §7.1, (7.2), p.28

import Mathlib
import Definitions.Def_RBMSensitivity_Data_M
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `M_0(x) := sup_{α ∈ U_0} M^α(x)` of (7.2): arXiv:1907.00472v2, p.28. The supremum is in `ℝ≥0∞`. -/
noncomputable def Data.M0 {J : ℕ} (D : Data J) (U₀ : Set ℝ) (x : E J) : ℝ≥0∞ :=
  ⨆ α ∈ U₀, D.M α x

end RBMSensitivity


