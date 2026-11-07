-- Prove2me | Definitions.Def_RobustFcstAgg_RandRule_loss
-- name    : RobustFcstAgg_RandRule_loss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:51:45.700484+00:00
-- url     : https://prove2.me/theorems/34eef691-bd7e-4740-b4da-1dac41a8658f
-- title:
--   Loss $L_{\mathcal D}(A)=\mathbb E_{\mathcal D}[(A-Y)^2]$
-- statement:
--   The expected squared error of the approximator implemented by a randomized rule under $\mathcal D$, also over the random context:
--   $$L_{\mathcal D}(A)=\mathbb E_{Z\sim P}\,\mathbb E_{\mathcal D}\bigl[(f_Z(\mathcal Q_Z)-Y)^2\bigr].$$
--
--   **Formalization Note** An extended-valued iterated integral, so that a non-integrable output has infinite loss.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.1, p.4; Example 2, p.5

import Mathlib
import Definitions.Def_RobustFcstAgg_RandRule
import Definitions.Def_RobustFcstAgg_Y
import Definitions.Def_RobustFcstAgg_Rule_output
import Definitions.Def_RobustFcstAgg_InfoStruct_jointLaw
open MeasureTheory
open scoped ENNReal

namespace RobustFcstAgg

/-- **Loss `L_D(A) = E_D[(A − Y)²]`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.1, p.4, and Example 2, p.5
("`L_D(A_P) = E_{D, i∼P}[(f_i(Q_i) − Y)²]`").

**Formalization Note.** An iterated `lintegral` in `ℝ≥0∞`, so a non-integrable output has infinite loss, not Bochner
`0`. -/
noncomputable def RandRule.loss {n : ℕ} (R : RandRule n) (D : InfoStruct n) : ℝ≥0∞ :=
  ∫⁻ z, ∫⁻ x, ENNReal.ofReal (((R.rule z).output D x - Y x) ^ 2) ∂D.jointLaw ∂(R.P)

end RobustFcstAgg


