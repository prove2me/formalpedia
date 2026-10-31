-- Prove2me | Definitions.Def_FoundationsRL_DECExamples_lipschitzClass
-- name    : FoundationsRL_DECExamples_lipschitzClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:45.254682+00:00
-- url     : https://prove2.me/theorems/059cec99-d0b9-4700-87cd-0e44dbf6b7e6
-- title:
--   Lipschitz bandit class $\mathcal F=\{f:\Pi\to[0,1]\mid f\text{ is }1\text{-Lipschitz w.r.t. }\rho\}$
-- statement:
--   Let $(\Pi,\rho)$ be a metric space. The **Lipschitz bandit** class is
--
--   $$
--   \mathcal F=\{f:\Pi\to[0,1]\mid |f(\pi)-f(\pi')|\le\rho(\pi,\pi')\text{ for all }\pi,\pi'\in\Pi\}.
--   $$
--
--   It is the standard nonparametric bandit class, for which the Decision-Estimation Coefficient decays slower than $\gamma^{-1}$.
--
--   **Formalization Note** The decision space is a type `D` with a `MetricSpace` instance whose `dist` is $\rho$; 1-Lipschitz is Mathlib's `LipschitzWith 1`.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.3.3, p. 73

import Mathlib

namespace FoundationsRL.DECExamples

/-- The Lipschitz bandit class `F = {f : D → [0, 1] | f is 1-Lipschitz w.r.t. ρ}` on a metric space
`(D, ρ)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §4.3.3, p. 73. -/
def lipschitzClass (D : Type*) [MetricSpace D] : Set (D → ℝ) :=
  {f | (∀ π, f π ∈ Set.Icc (0 : ℝ) 1) ∧ LipschitzWith 1 f}

end FoundationsRL.DECExamples


