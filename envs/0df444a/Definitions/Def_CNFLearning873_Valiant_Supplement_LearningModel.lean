-- Prove2me | Definitions.Def_CNFLearning873_Valiant_Supplement_LearningModel
-- name    : CNFLearning873_Valiant_Supplement_LearningModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:36:38.715058+00:00
-- url     : https://prove2.me/theorems/2dbb77ef-d9fe-48bb-83a9-bdbcc2c785c2
-- title:
--   Sample-only randomized CNF learners
-- statement:
--   A sample-only randomized learner maps an ordered sequence of Boolean assignments on $n$ variables to a probability distribution on CNF formulas on the same variables. It receives no unknown target or membership oracle; arbitrary private randomization and unbounded computation are allowed. If $F$ is satisfiable, a returned formula $G$ is successful precisely when it is satisfiable and
--
--   $$d_{\mathrm{TV}}(\mu_F,\mu_G)\le\varepsilon.$$
--
--   The success probability averages this event first over the learner's output law and then over the independent uniform-solution sample law $\mu_F^{\otimes T}$. This is the learning model used by the minimax lower bound.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Theorem 6.2 and its Appendix B proof, printed pp.27,37–38 = 1-based PDF pp.27,37–38; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Learner

noncomputable section

namespace CNFLearning873.Valiant.Supplement
open scoped BigOperators

/-- An arbitrary sample-only randomized proper learner. No target is an argument. -/
abbrev Learner (n T : ℕ) := (Fin T → Assignment n) → WildeQIT.FinDist (CNF n)

/-- TV success is only defined through nonempty solution laws. -/
def GoodOutput {n : ℕ} (F : CNF n) (h : (solutions F).Nonempty)
    (ε : ℝ) (G : CNF n) : Prop :=
  ∃ hg : (solutions G).Nonempty,
    HybridXorLift.tvDist (solutionLaw F h).prob (solutionLaw G hg).prob ≤ ε

/-- Integrates both the product sample law and the learner's private output law. -/
def learnerSuccess {n T : ℕ} (F : CNF n) (h : (solutions F).Nonempty)
    (ε : ℝ) (A : Learner n T) : ℝ :=
  ∑ xs, (sampleLaw F h T).prob xs * eventProb (A xs) (GoodOutput F h ε)

end CNFLearning873.Valiant.Supplement


