-- Prove2me | Definitions.Def_StaticProphetSec_expAR
-- name    : StaticProphetSec_expAR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:21.719655+00:00
-- url     : https://prove2.me/theorems/1bd3a102-d9c6-4643-a537-26a502f45944
-- title:
--   The expectation $\mathbb E[\mathrm{AR}_k(D)]$ for the policy $(t,p)$
-- statement:
--   For the policy $(t,p)$, this is
--
--   $$\mathbb E[\mathrm{AR}_k(D)],$$
--
--   where $D$ is the number of eligible applicants, and the expectation runs over the independent values and the tie-break coins. It is the second term of the lower bound in Lemma 1.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Lemma 1, p.17; Remark 1, p.5

import Mathlib
import Definitions.Def_StaticProphetSec_AR
import Definitions.Def_StaticProphetSec_accepted
import Definitions.Def_StaticProphetSec_coinProb

open MeasureTheory
open scoped ENNReal

namespace StaticProphetSec

/-- The expectation `E[AR_k(D)]` for the policy `(t, p)` (Arnosti & Ma, arXiv:2108.12893v2,
Lemma 1, p.17; Remark 1, p.5). `D` counts the eligible applicants, so the expectation runs over
the values and the tie-break coins.

**Formalization Note.** The integrand is bounded by `1`; the value lies in `ℝ≥0∞`. -/
noncomputable def expAR {n : ℕ} (k : ℕ) (μ : Fin n → Measure ℝ) (t p : ℝ) : ℝ≥0∞ :=
  ∫⁻ V, ∑ B : Fin n → Bool, coinProb p B * ENNReal.ofReal (AR k (demand t V B)) ∂Measure.pi μ

end StaticProphetSec


