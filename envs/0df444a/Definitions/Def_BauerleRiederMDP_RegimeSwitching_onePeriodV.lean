-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_onePeriodV
-- name    : BauerleRiederMDP_RegimeSwitching_onePeriodV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:27.040489+00:00
-- url     : https://prove2.me/theorems/4bafd0e0-0e27-46ba-891d-d683e4fd8abf
-- title:
--   Value $v(x)=\sup_{(c,a)\in D(x)}u(x,c,a)$ of the one-period problem
-- statement:
--   The value of the one-period consumption-investment problem is
--
--   $$
--   v(x)=\sup_{(c,a)\in D(x)}u(x,c,a),\qquad x\in[0,\infty),
--   $$
--
--   taken in $[-\infty,\infty]$; it is $+\infty$ when the market admits arbitrage.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.3, p.94 (PDF p.108)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_onePeriodD
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_onePeriodU
open MeasureTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The value of the one-period consumption-investment problem (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.3, p.94, PDF p.108):
`v(x) = sup_{(c,a) ∈ D(x)} u(x, c, a)`.

**Formalization Note.** The supremum is taken in `EReal`, so `v(x) = +∞` is representable (it
occurs when the market admits arbitrage). -/
noncomputable def onePeriodV {d : ℕ} (μ : Measure (Fin d → ℝ)) (i : ℝ) (Uc Up : ℝ → ℝ) (x : ℝ) :
    EReal :=
  ⨆ ca ∈ onePeriodD μ i x, onePeriodU μ i Uc Up x ca

end BauerleRiederMDP.RegimeSwitching


