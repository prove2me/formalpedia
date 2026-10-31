-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_confidenceSet
-- name    : FoundationsRL_E2DStructured_confidenceSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:50.157739+00:00
-- url     : https://prove2.me/theorems/35580830-6768-4e55-a550-9e293e9b6b4b
-- title:
--   The confidence sets $\mathcal F^t$
-- statement:
--   The confidence set at round $t$ of E2D with confidence sets, with radius $\beta$, is
--   $$\mathcal F^t=\Big\{f\in\mathcal F:\ \sum_{i<t}\mathbb E_{\pi^i\sim p^i}\big[(\hat f^i(\pi^i)-f(\pi^i))^2\big]\le\beta\Big\}.$$
--   It collects the functions consistent with the estimates produced so far.
--
--   **Formalization Note** The notes print $f^\star$ in the summand, which would make the condition independent of $f$. The set is the online-to-confidence-set conversion of footnote 13 and is read with $f$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.4.1, p. 75, and footnote 13

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_cumSqError

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The confidence set of E2D with confidence sets,
`F^t = {f ∈ F | ∑_{i<t} E_{π^i∼p^i}[(f̂^i(π^i) − f(π^i))²] ≤ β}`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.4.1, p. 75).

**Formalization Note.** The notes print `f⋆` in the summand, which makes the condition independent of
`f`; the set is the online-to-confidence-set conversion of footnote 13, and the summand is read with
`f`. -/
def confidenceSet {D : Type*} [MeasurableSpace D] (F : Set (D → ℝ)) (β : ℝ) (t : ℕ)
    (p : ℕ → ProbabilityMeasure D) (fhat : ℕ → D → ℝ) : Set (D → ℝ) :=
  {f ∈ F | ((cumSqError t p fhat f : ℝ≥0∞) : EReal) ≤ (β : EReal)}

end FoundationsRL.E2DStructured


