-- Prove2me | Definitions.Def_EffHorizonProphet_acceptProb
-- name    : EffHorizonProphet_acceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:34.244333+00:00
-- url     : https://prove2.me/theorems/a5d611d6-f8fc-4305-9df2-77019d080756
-- title:
--   The per-stage acceptance probability $p$
-- statement:
--   The **acceptance probability** of a rule is the probability $p=P(A_i)$ of the acceptance event at one stage. It does not depend on the stage.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Remark 16, p.31; p.21

import Mathlib
import Definitions.Def_EffHorizonProphet_Rule_Accepts
import Definitions.Def_EffHorizonProphet_stageLaw

open MeasureTheory

namespace EffHorizonProphet

/-- The **per-stage acceptance probability** `p = P(A_i)` of a rule (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Remark 16, p.31; p.21). -/
noncomputable def acceptProb (D : Measure ℝ) (ρ : Rule) : ℝ :=
  (stageLaw D).real {z | ρ.Accepts z.1 z.2}

end EffHorizonProphet


