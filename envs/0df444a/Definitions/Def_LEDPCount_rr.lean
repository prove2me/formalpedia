-- Prove2me | Definitions.Def_LEDPCount_rr
-- name    : LEDPCount_rr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:30.96927+00:00
-- url     : https://prove2.me/theorems/01f87a8d-bf7f-45b3-8829-6fd864848422
-- title:
--   Randomized response $\mathrm{RR}_\varepsilon$ and its debiased estimate (Definition 2.15, Lemma 2.17)
-- statement:
--   Given a privacy parameter $\varepsilon>0$ and a $t$-bit vector $a$, **randomized response** $\mathrm{RR}_\varepsilon(a)$ outputs a $t$-bit vector whose bits are randomized independently: bit $i$ equals $a_i$ with probability $e^{\varepsilon}/(e^{\varepsilon}+1)$ and $1-a_i$ otherwise. The **debiased estimate** of a reported bit $X\in\{0,1\}$ is
--   $$
--   Y=\frac{X(e^{\varepsilon}+1)-1}{e^{\varepsilon}-1}.
--   $$
--   These are the first-round primitive of LNC and the server's unbiased estimate of each adjacency bit.
--
--   **Formalization Note** Bits are Booleans, with true read as $1$. `rrBit ε b` is the law of one randomized bit and `rr ε a` the product law on $t$-bit vectors.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Definition 2.15 and Lemma 2.17, p.17 (PDF p.19); Algorithm 1 line 8, p.18 (PDF p.20)

import Mathlib

namespace LEDPCount

open MeasureTheory

/-- One bit of randomized response (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, Definition 2.15, p.17, PDF p.19): the bit
`b` is reported with probability `e^ε/(e^ε + 1)` and `1 − b` otherwise. Bits are `Bool`. -/
noncomputable def rrBit (ε : ℝ) (b : Bool) : Measure Bool :=
  ENNReal.ofReal (Real.exp ε / (Real.exp ε + 1)) • Measure.dirac b +
    ENNReal.ofReal (1 / (Real.exp ε + 1)) • Measure.dirac (!b)

/-- Definition 2.15 (Randomized Response) (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.17, PDF p.19): given `ε > 0` and a
`t`-bit vector `a`, `RR_ε(a)` outputs a `t`-bit vector whose bits are randomized
independently, bit `i` being `a_i` with probability `e^ε/(e^ε + 1)` and `1 − a_i` otherwise. -/
noncomputable def rr {t : ℕ} (ε : ℝ) (a : Fin t → Bool) : Measure (Fin t → Bool) :=
  Measure.pi fun i => rrBit ε (a i)

/-- The debiased estimate of a randomized-response bit (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, Lemma 2.17, p.17,
PDF p.19; Algorithm 1 line 8, p.18): `Y = (X(e^ε + 1) − 1)/(e^ε − 1)` for the reported bit
`X ∈ {0,1}` (`true ↦ 1`). -/
noncomputable def debias (ε : ℝ) (y : Bool) : ℝ :=
  ((Real.exp ε + 1) * (if y then 1 else 0) - 1) / (Real.exp ε - 1)

end LEDPCount


