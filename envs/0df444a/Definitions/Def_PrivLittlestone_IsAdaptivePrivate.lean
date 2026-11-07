-- Prove2me | Definitions.Def_PrivLittlestone_IsAdaptivePrivate
-- name    : PrivLittlestone_IsAdaptivePrivate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:30:41.186964+00:00
-- url     : https://prove2.me/theorems/edf6a3da-8659-456e-84bf-bb7013b9408f
-- title:
--   $(\varepsilon,\delta)$-privacy in the adaptive single-challenge model
-- statement:
--   An online learner is **$(\varepsilon, \delta)$-private in the adaptive single-challenge model** (Definition 2.1) if, for every single-challenge adversary strategy and every event $E$ of the adversary's view,
--   $$
--   \mathbb P_0[E] \le e^{\varepsilon}\, \mathbb P_1[E] + \delta
--   \qquad\text{and}\qquad
--   \mathbb P_1[E] \le e^{\varepsilon}\, \mathbb P_0[E] + \delta,
--   $$
--   where $\mathbb P_b$ is the law of the view when the learner receives the records of world $b$ and the same adversary strategy is used in both experiments.
--
--   **Formalization Note** With the adversary's coins fixed, the view is a function of the released classifiers, so events are sets of classifier transcripts; $E$ ranges over all of them.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Definition 2.1, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_playClassifiers
import Definitions.Def_PrivLittlestone_worldInput
import Definitions.Def_PrivLittlestone_IsSingleChallenge

namespace PrivLittlestone

open MeasureTheory

/-- **(ε, δ)-privacy in the adaptive single-challenge model** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Definition 2.1, p.4): for every single-challenge adversary strategy, the laws of the view in
worlds `b = 0` and `b = 1` satisfy the differential-privacy inequality in both directions, for
every event `E`.

**Formalization Note** The adversary is deterministic (fixed coins; see `Adversary`), so its view
(released classifiers, the pairs it supplied, its coins) is a function of the classifier
transcript and events on views are events on transcripts. `E` ranges over all sets of
transcripts. -/
def IsAdaptivePrivate {X : Type*} (A : OnlineLearner X) (T : ℕ) (ε δ : ℝ) : Prop :=
  ∀ adv : Adversary X T, IsSingleChallenge adv → ∀ E : Set (Fin T → X → Bool),
    A.μ {ω | playClassifiers A (worldInput adv false) ω ∈ E} ≤
        ENNReal.ofReal (Real.exp ε) * A.μ {ω | playClassifiers A (worldInput adv true) ω ∈ E} +
          ENNReal.ofReal δ ∧
      A.μ {ω | playClassifiers A (worldInput adv true) ω ∈ E} ≤
        ENNReal.ofReal (Real.exp ε) * A.μ {ω | playClassifiers A (worldInput adv false) ω ∈ E} +
          ENNReal.ofReal δ

end PrivLittlestone


