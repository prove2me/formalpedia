-- Prove2me | Definitions.Def_AnytimeAdaVR_tapeMeasure
-- name    : AnytimeAdaVR_tapeMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:41.307573+00:00
-- url     : https://prove2.me/theorems/e7beb38a-2bac-4f0c-bbde-d5873c907301
-- title:
--   Law of the random tape
-- statement:
--   Under the **tape law**, all optimization and validation samples are independent with the oracle's law $\mu$, all reservoir coins are independent and uniform on $[0,1]$, and the three families are independent of each other. This is the paper's "each path, its reservoir, and validation use independent random streams".
--
--   **Formalization Note** Infinite products of probability measures (`Measure.infinitePi`), combined by `Measure.prod`.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §2, p.4; §5.1, p.8; §5.3, p.10

import Mathlib
import Definitions.Def_AnytimeAdaVR_Tape

namespace AnytimeAdaVR

open MeasureTheory

/-- **The law of the random tape.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §2, p.4 ("Fresh samples are independent of the
preceding history"), §5.1, p.8 ("using an independent coin"), and §5.3, p.10 ("Each path, its
reservoir, and validation use independent random streams").

`tapeMeasure μ` is the product of: i.i.d. samples of law `μ` for every optimization coordinate,
i.i.d. uniform coins on `[0,1]` for every reservoir coordinate, and i.i.d. samples of law `μ` for
every validation coordinate, all independent.

**Formalization Note.** Products are `Measure.infinitePi` (an infinite product of probability
measures) and `Measure.prod`; `[0,1]` carries Mathlib's `volume` on `unitInterval`. -/
noncomputable def tapeMeasure {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) : Measure (Tape Ξ) :=
  (Measure.infinitePi fun _ : Path × ℕ => μ).prod
    ((Measure.infinitePi fun _ : Path × ℕ => (volume : Measure unitInterval)).prod
      (Measure.infinitePi fun _ : Path × ℕ × ℕ => μ))

end AnytimeAdaVR


