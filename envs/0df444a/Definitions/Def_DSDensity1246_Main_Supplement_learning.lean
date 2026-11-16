-- Prove2me | Definitions.Def_DSDensity1246_Main_Supplement_learning
-- name    : DSDensity1246_Main_Supplement_learning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:23:37.75321+00:00
-- url     : https://prove2.me/theorems/1e93d615-52ef-41c0-89d1-512a75162d56
-- title:
--   Randomized bounded-list learners and joint failure probability
-- statement:
--   For arbitrary data, label, and seed spaces X,Y,R and a natural list size ℓ, a list predictor maps x∈X to a finite set of at most ℓ distinct labels. A randomized list learner is a deterministic map A(ε,δ,m,S,r) returning such a predictor from an indexed sample S of length m and an independent seed r. The rule has no access to the distribution D or a target hypothesis.
--
--   For a benchmark b, its strict excess-error probability is
--
--   $$\Pr_{S\sim D^m,\,r\sim\rho}\!\left[\operatorname{err}_D(A(\varepsilon,\delta,m,S,r))>b+\varepsilon\right],\qquad
--   \operatorname{err}_D(\mu)=D\{(x,y):y\notin\mu(x)\}.$$
--
--   The same definition serves the realizable statements with b=0 and the agnostic statements with the best single-hypothesis error as b. Lists may be empty. There is no correctness guarantee in the learner type.
--
--   **Formalization Note** Samples are indexed by Fin m. Accuracy and confidence are conventional optional inputs; a learner that ignores either is included. Arbitrary lawful seed distributions and outer event probabilities are allowed. Probability is taken under the independently constructed product sampling law.
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), pp. 12–13, §3; pp. 19–23 and p. 33

import Definitions.Def_DSDensity1246_Main_Supplement_probability

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DSDensity1246.Main.Supplement

/-- §3: a finite list of at most ℓ distinct labels at every point; empty lists are allowed. -/
def ListPredictor (X Y : Type*) (ℓ : ℕ) := X → {L : Finset Y // L.card ≤ ℓ}

/-- A distribution-independent randomized learner; accuracy/confidence can be supplied
as usual PAC parameters. The seed law is separate from this deterministic map. -/
def ListLearner (X Y R : Type*) (ℓ : ℕ) :=
  ℝ → ℝ → (m : ℕ) → (Fin m → X × Y) → R → ListPredictor X Y ℓ

/-- §3: list population error. No probability map is supplied by the learner. -/
noncomputable def listError {X Y : Type*} {ℓ : ℕ}
    (D : DataLaw (X × Y)) (μ : ListPredictor X Y ℓ) : ℝ≥0∞ :=
  letI : MeasurableSpace (X × Y) := D.1
  (D.2 : Measure (X × Y)) {z | z.2 ∉ (μ z.1).1}

/-- Probability of strict excess error, over BOTH iid data and independent randomness.
The threshold is 0+ε for realizable learning and bestError+ε for agnostic learning. -/
noncomputable def failureProbability {X Y R : Type*}
    [MeasurableSpace R] {ℓ : ℕ}
    (D : DataLaw (X × Y)) (ρ : ProbabilityMeasure R)
    (A : ListLearner X Y R ℓ) (ε δ : ℝ) (m : ℕ) (benchmark : ℝ≥0∞) : ℝ≥0∞ :=
  letI : MeasurableSpace (X × Y) := D.1
  trainingLaw D ρ m {t | benchmark + ENNReal.ofReal ε < listError D (A ε δ m t.1 t.2)}

end DSDensity1246.Main.Supplement


