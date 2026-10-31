-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_OnlineRegressionGuarantee
-- name    : FoundationsRL_E2DStructured_OnlineRegressionGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:27.339031+00:00
-- url     : https://prove2.me/theorems/ae44d43e-1d5f-4234-8b2e-c18f559744f5
-- title:
--   The online regression oracle guarantee (Definition 7)
-- statement:
--   Let $(\Omega,P)$ be a probability space carrying distributions $p^t$ and estimates $\hat f^t$. The **online regression guarantee** with error bound $\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta)$ says that with probability at least $1-\delta$,
--   $$\sum_{t=1}^T\mathbb E_{\pi^t\sim p^t}\big[(\hat f^t(\pi^t)-f^\star(\pi^t))^2\big]\le\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta).$$
--   This is the only property of the estimation oracle on which the E2D analysis rests.
--
--   **Formalization Note** The definition is the guarantee on the realized sequences: $p^t$ and $\hat f^t$ are arbitrary functions of the outcome $\omega$, so every adaptive protocol as in Definition 7 is covered. The probability of the event is read with the outer measure when the event is not measurable.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Definition 7, p. 64

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_cumSqError

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The guarantee of an online regression oracle (Definition 7): with probability at least `1 − δ`,
`∑_{t=1}^T E_{π^t∼p^t}[(f̂^t(π^t) − f⋆(π^t))²] ≤ EstSq`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, Definition 7, p. 64).

**Formalization Note.** `p t ω` and `fhat t ω` are the distribution and the estimate of round `t` on
outcome `ω`; `est` is the number `EstSq(F, T, δ)`. The definition records the guarantee on the realized
sequences and imposes no adaptedness, so it applies to every protocol of the form of Definition 7.
The measure of the event is an outer measure when the event is not measurable, which is at least as
demanding as a lower bound on a measurable subset. The comparison is in `EReal`, so the bound is not
truncated at `0`. -/
def OnlineRegressionGuarantee {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℕ) (δ est : ℝ) (p : ℕ → Ω → ProbabilityMeasure D)
    (fhat : ℕ → Ω → D → ℝ) (fstar : D → ℝ) : Prop :=
  ENNReal.ofReal (1 - δ) ≤
    P {ω | ((cumSqError T (fun t => p t ω) (fun t => fhat t ω) fstar : ℝ≥0∞) : EReal) ≤ (est : EReal)}

end FoundationsRL.E2DStructured


