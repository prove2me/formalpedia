-- Prove2me | Definitions.Def_PrivLittlestone_continualLearner
-- name    : PrivLittlestone_continualLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:42:17.870595+00:00
-- url     : https://prove2.me/theorems/76e0860c-ce13-40a8-b839-74fe759db6c5
-- title:
--   Algorithm 1 (continual learning from a ranked candidate system) as an online learner
-- statement:
--   **Algorithm 1**, run on its public inputs, is an online learner: its coins are those of Algorithm 1, and the classifier $g_t$ released at round $t$ is the phase aggregate of the current phase (or $g_{\mathrm{fb}}$ after the phase cap), each released before its labeled example. This is the learner of Theorem 4.1, and with the Littlestone candidate system of Proposition 5.1, majority aggregation and the identity filter, the learner of Theorem 1.1.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Algorithm 1, p.7

import Mathlib
import Definitions.Def_PrivLittlestone_OnlineLearner
import Definitions.Def_PrivLittlestone_algState__7d3f58
import Definitions.Def_PrivLittlestone_coinMeasure

namespace PrivLittlestone

/-- **Algorithm 1, continual learning from a ranked candidate system**, as an online learner
(He–He, *Private Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission
manuscript (sha256 21480556…c562), Algorithm 1, p.7): the coins are those of `coinMeasure`, and
the classifier released at round `t` is the current classifier of the replayed state after the
first `t` records (`g_t ← g` within a phase, `g_t ← g_fb` after the cap). -/
noncomputable def continualLearner {X Z U : Type*} {D : ℕ} {B : ℝ} (P : Alg1Spec X Z U D B) :
    OnlineLearner X where
  Ω := Alg1Coins P
  mΩ := inferInstance
  μ := coinMeasure P
  release := fun t hist ω => (algState P ω t hist).current

end PrivLittlestone


