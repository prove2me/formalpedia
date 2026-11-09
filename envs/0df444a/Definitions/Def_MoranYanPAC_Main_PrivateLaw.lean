-- Prove2me | Definitions.Def_MoranYanPAC_Main_PrivateLaw
-- name    : MoranYanPAC_Main_PrivateLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:04:56.460576+00:00
-- url     : https://prove2.me/theorems/34e7a9bf-fc68-43ae-ac8f-2568622ea970
-- title:
--   Probability laws and insertion/deletion privacy
-- statement:
--   A randomized rule $A$ sends every finite ordered input list to a probability mass function on an arbitrary output universe $Y$. For an event $E\subseteq Y$, write $A(S)(E)$ for its probability. These laws are countably additive probabilities on all output subsets, even when $Y$ itself is uncountable. The source's constructed rules have finite support on each input.
--
--   The rule is **$(\varepsilon,\delta)$-differentially private** when
--
--   $$\forall S\sim T,\ \forall E\subseteq Y,\qquad A(S)(E)\le e^\varepsilon A(T)(E)+\delta.$$
--
--   Here $S\sim T$ is the referenced arbitrary-position insertion/deletion adjacency. The quantifiers include both ordered directions and every input, including unrealizable samples and the empty sample. The PMF type supplies normalization; a zero measure is not an algorithm. Privacy remains a separate predicate to be proved.
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Sections 2.2 and 4.1, pp. 4 and 14 (PDF pp. 4 and 14)

import Mathlib
import Definitions.Def_PrivLittlestone_IsInsDelNeighbor

set_option autoImplicit false

open scoped ENNReal

namespace MoranYanPAC.Main

/-- Event probability of a discrete probability law. This is a countably additive
probability on the full powerset, not a default value of Measure.map. -/
noncomputable def eventProbability {Y : Type*} (p : PMF Y) (E : Set Y) : ℝ≥0∞ :=
  p.toOuterMeasure E

/-- Section 4.1, p. 14. Privacy on all finite ordered inputs and all output events. -/
def Private {Z Y : Type*} (A : List Z → PMF Y) (ε δ : ℝ) : Prop :=
  ∀ S T : List Z, PrivLittlestone.IsInsDelNeighbor S T → ∀ E : Set Y,
    eventProbability (A S) E ≤ ENNReal.ofReal (Real.exp ε) *
      eventProbability (A T) E + ENNReal.ofReal δ

end MoranYanPAC.Main


