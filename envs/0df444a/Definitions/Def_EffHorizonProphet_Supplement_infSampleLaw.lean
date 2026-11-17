-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_infSampleLaw
-- name    : EffHorizonProphet_Supplement_infSampleLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:56:47.810793+00:00
-- url     : https://prove2.me/theorems/5dd46d6e-4958-4f2b-a9e1-74adb367cf8c
-- title:
--   Law of the infinite i.i.d. sequence of stages
-- statement:
--   The law of the infinite sequence $((Y_i,U_i))_{i\ge1}$ of i.i.d. stage pairs, each with base reward $Y_i\sim D$ and an independent uniform coin $U_i$.
--
--   **Formalization Note** Mathlib's `Measure.infinitePi` of the published `stageLaw D`; stages are numbered from $0$. It is a probability measure for every admissible $D$ (sanity file).
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 7, p.11

import Mathlib
import Definitions.Def_EffHorizonProphet_stageLaw

open MeasureTheory

namespace EffHorizonProphet.Supplement

/-- The law of the **infinite sequence** of stage pairs `(Y_i, U_i)_{i ≥ 1}` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 7,
p.11): i.i.d. base rewards `Y_i ∼ D`, each with an independent uniform coin `U_i`.

**Formalization Note** Stages are `0`-based (`ℕ` indexes `i = 1, 2, …` as `0, 1, …`). Mathlib's
`Measure.infinitePi` is the product of the probability measures `stageLaw D`; it is the zero
measure when `D` is not a probability measure, which never happens for an admissible law. -/
noncomputable def infSampleLaw (D : Measure ℝ) : Measure (ℕ → ℝ × unitInterval) :=
  Measure.infinitePi fun _ : ℕ => stageLaw D

end EffHorizonProphet.Supplement


