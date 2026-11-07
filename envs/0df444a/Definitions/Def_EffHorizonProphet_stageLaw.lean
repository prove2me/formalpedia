-- Prove2me | Definitions.Def_EffHorizonProphet_stageLaw
-- name    : EffHorizonProphet_stageLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:46.381418+00:00
-- url     : https://prove2.me/theorems/a5e78a73-108d-490a-bde2-6cf8cb814024
-- title:
--   Law of one stage $(Y_i,U_i)$
-- statement:
--   The **stage law** is the law of the pair $(Y_i,U_i)$: the base reward $Y_i\sim D$ and an independent coin $U_i$ uniform on $[0,1]$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.3; Remark 16, p.31

import Mathlib

open MeasureTheory

namespace EffHorizonProphet

/-- The law of one stage's pair `(Y_i, U_i)` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.3; Remark 16, p.31): the base
reward `Y_i ∼ D` and an independent uniform coin `U_i`. -/
noncomputable def stageLaw (D : Measure ℝ) : Measure (ℝ × unitInterval) :=
  D.prod volume

end EffHorizonProphet


