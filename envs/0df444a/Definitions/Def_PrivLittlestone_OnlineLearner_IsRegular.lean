-- Prove2me | Definitions.Def_PrivLittlestone_OnlineLearner_IsRegular
-- name    : PrivLittlestone_OnlineLearner_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:44.302666+00:00
-- url     : https://prove2.me/theorems/4fecf670-8c24-42ca-8935-fb88b9b3eaed
-- title:
--   Regular online learner: probability coins, countable measurable releases
-- statement:
--   An online learner is **regular up to horizon $T$** if its coin law $\mu$ is a probability measure and, at every round $t < T$ and every record history, the released classifier, viewed as a function of the coins $\omega$, takes countably many values and has a measurable preimage of every set of classifiers.
--
--   This is the paper's standing convention that "hypothesis evaluations and selection rules are measurable" and that candidate distributions have finite support. It makes every event of the released transcript measurable, so that the privacy inequalities can be imposed on all sets of transcripts.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_OnlineLearner

namespace PrivLittlestone

open MeasureTheory

/-- **Regularity** of an online learner up to horizon `T` (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
§2, p.4: "Hypothesis evaluations and selection rules are measurable"; "Candidate distributions
have finite support"): the coin law is a probability measure, and at every round `t < T` and
every record history the released classifier, as a function of the coins, takes countably many
values and has a measurable preimage of every set of classifiers.

**Formalization Note** Countable range plus measurable fibres makes every event of the released
transcript measurable, for fixed streams and in the adaptive game, so the privacy inequalities
can quantify over all sets of transcripts. -/
def OnlineLearner.IsRegular {X : Type*} (A : OnlineLearner X) (T : ℕ) : Prop :=
  IsProbabilityMeasure A.μ ∧
    ∀ t : ℕ, t < T → ∀ hist : Fin t → X × Bool,
      (Set.range (A.release t hist)).Countable ∧
        ∀ s : Set (X → Bool), MeasurableSet (A.release t hist ⁻¹' s)

end PrivLittlestone


