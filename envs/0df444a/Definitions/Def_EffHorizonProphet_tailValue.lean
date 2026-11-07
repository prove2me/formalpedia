-- Prove2me | Definitions.Def_EffHorizonProphet_tailValue
-- name    : EffHorizonProphet_tailValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:40.999726+00:00
-- url     : https://prove2.me/theorems/edbfbdfc-2d01-4efa-b649-0f08bea79a77
-- title:
--   The truncated tail moment $\mathbb E[Y\mathbf 1\{A\}]$
-- statement:
--   The **truncated tail moment** of a rule is $\mathbb E[Y\mathbf 1\{A\}]$, for one stage with acceptance event $A$. It is the paper's $\mathbb E[Y\mathbf 1\{Y>\alpha_1\}]$, with the exceedance event replaced by the randomized acceptance event of Remark 16.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), p.9; Remark 16, p.31

import Mathlib
import Definitions.Def_EffHorizonProphet_Rule_Accepts
import Definitions.Def_EffHorizonProphet_stageLaw

open MeasureTheory

namespace EffHorizonProphet

open scoped Classical in
/-- The **truncated tail moment** `E[Y 1{A}]` of a rule (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.9 and Remark 16, p.31), the paper's
`E[Y 1{Y > α₁}]` with the acceptance event in place of the exceedance event. -/
noncomputable def tailValue (D : Measure ℝ) (ρ : Rule) : ℝ :=
  ∫ z, (if ρ.Accepts z.1 z.2 then z.1 else 0) ∂stageLaw D

end EffHorizonProphet


