-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_ContextualOnlineRegressionGuarantee
-- name    : FoundationsRL_E2DStructured_ContextualOnlineRegressionGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:46.86499+00:00
-- url     : https://prove2.me/theorems/f321e17b-c9a8-44d3-88dc-28d7ee2c9975
-- title:
--   The contextual online regression guarantee
-- statement:
--   Let contexts $x^t$, distributions $p^t$ and estimates $\hat f^t:\mathcal X\times\Pi\to\mathbb R$ live on a probability space. The **contextual online regression guarantee** says that with probability at least $1-\delta$,
--   $$\sum_{t=1}^T\mathbb E_{\pi^t\sim p^t}\big[(\hat f^t(x^t,\pi^t)-f^\star(x^t,\pi^t))^2\big]\le\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta).$$
--
--   **Formalization Note** As in the non-contextual case, the guarantee is on realized sequences. Contexts may depend on the outcome in any way, which covers the adversarial contexts of the notes.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.5, p. 78

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_sqError

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The contextual estimation guarantee: with probability at least `1 − δ`,
`∑_{t=1}^T E_{π^t∼p^t}[(f̂^t(x^t, π^t) − f⋆(x^t, π^t))²] ≤ EstSq`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.5, p. 78).

**Formalization Note.** As in `OnlineRegressionGuarantee`, the guarantee is on realized sequences, with
contexts `x t ω` of arbitrary dependence, which covers the adversarial contexts of the notes. -/
def ContextualOnlineRegressionGuarantee {X D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℕ) (δ est : ℝ) (x : ℕ → Ω → X) (p : ℕ → Ω → ProbabilityMeasure D)
    (fhat : ℕ → Ω → X → D → ℝ) (fstar : X → D → ℝ) : Prop :=
  ENNReal.ofReal (1 - δ) ≤
    P {ω | ((∑ t ∈ Finset.range T, sqError (p t ω) (fhat t ω (x t ω)) (fstar (x t ω)) : ℝ≥0∞) : EReal)
        ≤ (est : EReal)}

end FoundationsRL.E2DStructured


