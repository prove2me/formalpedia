-- Prove2me | Definitions.Def_PrivLittlestone_OnlineLearner
-- name    : PrivLittlestone_OnlineLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:49.35106+00:00
-- url     : https://prove2.me/theorems/064484c5-6274-4fb5-9d94-222828fb223d
-- title:
--   Online learner: coins and causal classifier releases
-- statement:
--   An **online learner** for binary classification over an instance space $X$ consists of a probability space of coins $(\Omega, \mu)$ and, for every round $t$ and every history $z_1, \dots, z_t$ of labeled examples $z_i = (x_i, y_i) \in X \times \{0,1\}$, a classifier
--   $$
--   g_{t+1} = \mathrm{release}_t(z_1, \dots, z_t; \omega) : X \to \{0,1\}.
--   $$
--   At round $t+1$ the learner releases $g_{t+1}$, determined by the preceding data and its randomness, and only then receives $z_{t+1}$.
--
--   This is the object whose transcript is protected by the privacy notions of the mission and whose mistakes are counted by the accuracy guarantees.
--
--   **Formalization Note** Rounds are $0$-based: `release t hist ω` is the paper's $g_{t+1}$. Causality is built into the type: the classifier at round $t$ sees only the first $t$ records. The labels $\{0,1\}$ are `Bool`. That $\mu$ is a probability measure and that releases are measurable are stated separately (`OnlineLearner.IsRegular`).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §1.1, p.1, and §2.1, p.4

import Mathlib

namespace PrivLittlestone

open MeasureTheory

/-- An **online learner** for binary classification over an instance type `X` (He–He, *Private
Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript
(sha256 21480556…c562), §1.1 and §2.1, pp.1, 4): a probability space of coins `(Ω, μ)` and, for
every round `t` and every history of the `t` labeled examples received so far, the classifier
`g : X → {0,1}` released at that round as a function of the coins.

**Formalization Note** Rounds are 0-based: `release t hist ω` is the paper's `g_{t+1}`, released
after the records `z_1, …, z_t` (`hist`) and before `z_{t+1}`. Causality ("determined by preceding
data and its randomness", "each released before its labeled example") is the type of `release`:
the classifier at round `t` sees only the first `t` records. `{0,1}` is `Bool`. The structure
carries no proof fields; that `μ` is a probability measure and that releases are measurable are
stated by `OnlineLearner.IsRegular`. -/
structure OnlineLearner (X : Type*) where
  /-- the coin space -/
  Ω : Type
  /-- the σ-algebra of the coin space -/
  mΩ : MeasurableSpace Ω
  /-- the law of the coins -/
  μ : @Measure Ω mΩ
  /-- `release t hist ω`: the classifier released at the 0-based round `t` after the records
  `hist`, on coins `ω` -/
  release : (t : ℕ) → (Fin t → X × Bool) → Ω → X → Bool

instance {X : Type*} (A : OnlineLearner X) : MeasurableSpace A.Ω := A.mΩ

end PrivLittlestone


