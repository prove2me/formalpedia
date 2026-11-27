-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_IsUniversallyMeasurable
-- name    : BauerleRiederMDP_LQ_Supplement_IsUniversallyMeasurable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:10:09.222048+00:00
-- url     : https://prove2.me/theorems/4502a3ef-d524-4947-9c7b-597b4ddc7bff
-- title:
--   Universal measurability
-- statement:
--   **Universal measurability** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Remark 2.3.14 and §7.4, the measurability class of the value functions of Borel models; standard notion, e.g. Bertsekas–Shreve 1978, Def. 7.18): a function $v : E \to  [-\infty , \infty ]$ is universally measurable if it is measurable with respect to the completion of every probability measure on $E$.
--
--   **Formalization Note.** Stated as: $v$ is almost-everywhere measurable with respect to every probability measure $\mu $ on $E$ (`AEMeasurable v μ`, i.e. it agrees $\mu $-a.e. with a measurable function), which is measurability with respect to the $\mu $-completion.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 2.3.14 and §7.4, the measurability class of the value functions of Borel models; standard notion, e.g. Bertsekas–Shreve 1978, Def. 7.18

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **Universal measurability** (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), Remark 2.3.14 and §7.4, the measurability class of the value functions of Borel
models; standard notion, e.g. Bertsekas–Shreve 1978, Def. 7.18): a function `v : E → [−∞, ∞]` is
universally measurable if it is measurable with respect to the completion of every probability
measure on `E`.

**Formalization Note.** Stated as: `v` is almost-everywhere measurable with respect to every
probability measure `μ` on `E` (`AEMeasurable v μ`, i.e. it agrees `μ`-a.e. with a measurable
function), which is measurability with respect to the `μ`-completion. -/
def IsUniversallyMeasurable {E : Type*} [MeasurableSpace E] (v : E → EReal) : Prop :=
  ∀ μ : Measure E, IsProbabilityMeasure μ → AEMeasurable v μ

end BauerleRiederMDP.LQ.Supplement


