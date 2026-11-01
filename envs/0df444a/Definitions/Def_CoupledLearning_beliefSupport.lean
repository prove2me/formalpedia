-- Prove2me | Definitions.Def_CoupledLearning_beliefSupport
-- name    : CoupledLearning_beliefSupport
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:36.319843+00:00
-- url     : https://prove2.me/theorems/581140c2-b075-4c0f-a5da-bbffd20af26d
-- title:
--   Support $[\theta]$ of a belief
-- statement:
--   The support of a belief $\theta$ is
--
--   $$[\theta]=\{s\in S\mid\theta(s)>0\}.$$
--
--   It appears in condition (2a) of Theorem 1.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Theorem 1, p.12

import Mathlib

namespace CoupledLearning

/-- The support `[θ] = {s ∈ S | θ(s) > 0}` of a belief `θ` (arXiv:2206.05637v2, Theorem 1,
p.12). -/
def beliefSupport {S : Type*} (θ : S → ℝ) : Set S :=
  {s | 0 < θ s}

end CoupledLearning


