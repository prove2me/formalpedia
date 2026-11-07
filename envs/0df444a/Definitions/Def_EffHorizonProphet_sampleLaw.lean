-- Prove2me | Definitions.Def_EffHorizonProphet_sampleLaw
-- name    : EffHorizonProphet_sampleLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:40.65033+00:00
-- url     : https://prove2.me/theorems/0179ae1a-12a7-4d33-a184-fb7cb9c61a06
-- title:
--   Law of the whole horizon
-- statement:
--   Given a phase-length profile $L=(L(s))_{s<S}$ with $n=\sum_s L(s)$, the **sample law** is the law of $n$ independent pairs $(Y_i,U_i)$, each with the stage law. The $Y_i$ are i.i.d. from $D$ and the coins are i.i.d. uniform and independent of them.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.3; Remark 16, p.31

import Mathlib
import Definitions.Def_EffHorizonProphet_stageLaw

open MeasureTheory

namespace EffHorizonProphet

/-- The law of the whole horizon (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.3; Remark 16, p.31): `n = ∑ s, L s` i.i.d.
pairs `(Y_i, U_i)`.

**Formalization Note** `L : Fin S → ℕ` is the phase-length profile, with `n_s = L s`. The coins are
coordinates of the sample space, as Remark 16 introduces them. -/
noncomputable def sampleLaw {S : ℕ} (D : Measure ℝ) (L : Fin S → ℕ) :
    Measure (Fin (∑ s, L s) → ℝ × unitInterval) :=
  Measure.pi fun _ => stageLaw D

end EffHorizonProphet


