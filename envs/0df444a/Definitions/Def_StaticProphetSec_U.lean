-- Prove2me | Definitions.Def_StaticProphetSec_U
-- name    : StaticProphetSec_U
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:12.682987+00:00
-- url     : https://prove2.me/theorems/ed8196a1-4918-4079-b5a6-a0ef8e587e2f
-- title:
--   $U(t,F)=\mathbb E[\sum_i\max(V_i-t,0)]$
-- statement:
--   For a threshold $t$,
--
--   $$U(t,F)=\mathbb E_{V\sim F}\Big[\sum_{i=1}^n\max(V_i-t,0)\Big].$$
--
--   **Formalization Note** The value lies in $[0,\infty]$.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, (28), p.32

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace StaticProphetSec

/-- `U(t, F) = E[∑ i, max(V_i - t, 0)]`, equation (28) (Arnosti & Ma, arXiv:2108.12893v2, (28),
p.32). The value lies in `ℝ≥0∞`, so it may be `∞`. -/
noncomputable def U {n : ℕ} (t : ℝ) (μ : Fin n → Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ V, ∑ i, ENNReal.ofReal (max (V i - t) 0) ∂Measure.pi μ

end StaticProphetSec


